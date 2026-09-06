"""Undefined-name scan for the plugin sources.

importlib.reload re-executes a module into its existing namespace, so a
definition deleted by an edit keeps working in the hot-reloaded process and
only fails on a cold import. This catches that before Binary Ninja does.
"""
import ast
import builtins
import glob
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
IMPLICIT = {"__file__", "__name__", "__doc__", "__package__", "__spec__"}


def module_bindings(tree):
    names = set(dir(builtins)) | IMPLICIT
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                for n in ast.walk(target):
                    if isinstance(n, ast.Name):
                        names.add(n.id)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                names.add((alias.asname or alias.name).split(".")[0])
    return names


class Checker(ast.NodeVisitor):
    def __init__(self, path, module_names):
        self.path = path
        self.module_names = module_names
        self.scopes = [set()]
        self.problems = []

    def visit_FunctionDef(self, node):
        local = {a.arg for a in node.args.args + node.args.kwonlyargs + node.args.posonlyargs}
        for extra in (node.args.vararg, node.args.kwarg):
            if extra is not None:
                local.add(extra.arg)
        for n in ast.walk(node):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
                local.add(n.id)
            elif isinstance(n, (ast.FunctionDef, ast.ClassDef)):
                local.add(n.name)
            elif isinstance(n, ast.arg):
                local.add(n.arg)
            elif isinstance(n, (ast.Import, ast.ImportFrom)):
                for alias in n.names:
                    local.add((alias.asname or alias.name).split(".")[0])
            elif isinstance(n, ast.ExceptHandler) and n.name:
                local.add(n.name)
        self.scopes.append(local)
        self.generic_visit(node)
        self.scopes.pop()

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_ClassDef(self, node):
        self.scopes.append({n.name for n in node.body if isinstance(n, ast.FunctionDef)})
        self.generic_visit(node)
        self.scopes.pop()

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load) and node.id not in self.module_names \
                and not any(node.id in s for s in self.scopes):
            self.problems.append("%s:%d undefined name %r" % (self.path, node.lineno, node.id))


def main():
    problems = []
    for path in sorted(glob.glob(os.path.join(ROOT, "oorecover", "*.py"))) + [os.path.join(ROOT, "__init__.py")]:
        tree = ast.parse(open(path).read(), path)
        checker = Checker(os.path.relpath(path, ROOT), module_bindings(tree))
        checker.visit(tree)
        problems.extend(checker.problems)
    for p in problems:
        print(p)
    print("undefined names: %d" % len(problems))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())

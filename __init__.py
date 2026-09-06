"""OORecover Binary Ninja plugin entry point."""
import json
import os
import threading
import traceback

from binaryninja import BackgroundTaskThread, PluginCommand
from binaryninja.log import Logger

_log = Logger(0, "oorecover")
_HERE = os.path.dirname(os.path.abspath(__file__))
_AUTOTEST = os.path.join(_HERE, "tests", "autotest.txt")
_REPORTS = os.path.join(_HERE, "tests", "reports")


class _Recover(BackgroundTaskThread):
    def __init__(self, bv):
        super().__init__("OORecover: starting", True)
        self.bv = bv

    def _progress(self, text):
        self.progress = "OORecover: " + text

    def run(self):
        try:
            from .oorecover import run_and_apply
            result = run_and_apply(self.bv, log=_log.log_info, progress=self._progress,
                                   cancelled=lambda: self.cancelled)
            if result is not None:
                _log.log_info("oorecover: %d classes (%s ABI)"
                              % (len(result.classes), result.abi))
        except Exception:
            _log.log_error("oorecover failed:\n" + traceback.format_exc())
        finally:
            self.finish()


def _command(bv):
    _Recover(bv).start()


def _report(bv, result):
    from .oorecover.report import build_report
    return build_report(bv, result)


_PIPELINE_MODULES = ("facts", "names", "abi", "itanium", "msvc", "scan", "collect", "validate", "model", "apply", "report")


def _reload_pipeline():
    """Re-import the pipeline in dependency order so edits apply without a restart."""
    import importlib
    import sys
    pkg = __name__ + ".oorecover"
    for name in _PIPELINE_MODULES:
        mod = sys.modules.get(pkg + "." + name)
        if mod is not None:
            importlib.reload(mod)
    top = sys.modules.get(pkg)
    if top is not None:
        importlib.reload(top)
    return importlib.import_module(pkg).run_and_apply


def _autotest_once(targets, logf):
    import binaryninja

    def log(msg):
        _log.log_info(msg)
        logf.write(msg + "\n")
        logf.flush()

    run_and_apply = _reload_pipeline()
    keep_open = "#keep" in targets
    trace = [int(t.split()[1], 0) for t in targets if t.startswith("#trace ")]
    for path in (t for t in targets if not t.startswith("#")):
        bv = None
        base = os.path.basename(path)
        try:
            log("=== %s" % base)
            bv = binaryninja.load(path)
            if bv is None:
                raise RuntimeError("load returned None")
            bv.update_analysis_and_wait()
            if trace:
                from .oorecover import trace_functions
                trace_functions(bv, trace, log)
                continue
            result = run_and_apply(bv, log=log)
            if result is None:
                raise RuntimeError("pipeline returned nothing")
            out = os.path.join(_REPORTS, base + ".json")
            with open(out, "w") as f:
                json.dump(_report(bv, result), f, indent=1)
            log("autotest: %s done (%d classes) -> %s" % (base, len(result.classes), out))
        except Exception:
            msg = "autotest %s failed:\n%s" % (base, traceback.format_exc())
            _log.log_error(msg)
            logf.write(msg + "\n")
            logf.flush()
        finally:
            if bv is not None and not keep_open:
                try:
                    bv.file.close()
                except Exception:
                    pass


def _autotest_watch():
    import time
    while True:
        if os.path.isfile(_AUTOTEST):
            try:
                with open(_AUTOTEST) as f:
                    targets = [ln.strip() for ln in f if ln.strip()]
                # Claim the request before running it: a run killed halfway
                # through must not start itself again on the next launch.
                os.unlink(_AUTOTEST)
                os.makedirs(_REPORTS, exist_ok=True)
                done = os.path.join(_REPORTS, "autotest.done")
                if os.path.isfile(done):
                    os.unlink(done)
                with open(os.path.join(_REPORTS, "autotest.log"), "w") as logf:
                    _autotest_once(targets, logf)
                with open(done, "w") as f:
                    f.write(time.strftime("%T") + "\n")
            except Exception:
                _log.log_error("autotest watcher failed:\n" + traceback.format_exc())
        time.sleep(2)


if os.path.isdir(os.path.join(_HERE, "tests")):
    threading.Thread(target=_autotest_watch, name="OORecoverAutotest", daemon=True).start()

PluginCommand.register(
    "OORecover\\Recover C++ Classes",
    "Recover C++ classes from vtables, RTTI (Itanium and MSVC), and MLIL dataflow",
    _command,
)

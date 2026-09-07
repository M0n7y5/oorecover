#ifdef _MSC_VER
typedef decltype(sizeof(0)) size_t;
extern "C" int _purecall() { return 0; }
static char pool[65536];
static size_t used;
void* operator new(size_t n) { void* p = pool + used; used += (n + 15) & ~(size_t)15; return p; }
void operator delete(void*, size_t) {}
void operator delete(void*) {}
#else
#include <cstddef>
#endif

int g_naps;

namespace zoo {

// Returned by value: too big for registers, so the caller passes a hidden
// buffer pointer in the first argument register and this moves to the second.
struct Info { long v[5]; };

// Also returned through the hidden buffer (24 bytes). Vec is only ever
// copied into it, so the plugin keeps a placeholder for it; Label is built
// in it by its constructor, which names the result type.
struct Vec { long x, y, z; };
class Label {
public:
    Label(int i);
    long id, pad, extra;
};

class Animal {
public:
    Animal() { age = 0; tag = 1; }
    virtual ~Animal() { tag = -1; }
    virtual int speak() { return age; }
    virtual int legs() { return 4; }
    virtual int describe() { return speak() * 100 + legs(); }
    virtual Info info() { Info i; for (int k = 0; k < 5; k++) i.v[k] = age + k; return i; }
    virtual Info info2(int k, long j) { Info i; i.v[0] = age + k; i.v[1] = j; i.v[2] = age + k * j; i.v[3] = k - j; i.v[4] = age - j; return i; }
    virtual Label label() { return Label(age); }
    virtual Label label2();
    int rate(int k);
    int age;
    long tag;
};

class Dog : public Animal {
public:
    ~Dog() override {}
    int speak() override { return age + tricks; }
    virtual void bark() { tricks++; }
    Label label() override { return Label(age + tricks); }
    // Identical to Cat::kind: -O2 folds the two into one function that both
    // vtables list; Animal is their common base.
    virtual int kind() { return 3; }
    int tricks;
};

// Two levels deep: a Puppy method reads its vtable through the base chain
// (_base_Dog._base_Animal._vftable, typed as Animal's VTable) and calls a
// slot past that VTable's width. Speculative devirtualisation at -O2 guards
// the slot with a compare against the expected function; rest() becomes a
// tail dispatch (jmp [rax+slot]) at -O2 once speculation is off for it.
class Puppy : public Dog {
public:
    ~Puppy() override { g_naps++; }   // a side effect keeps --icf from folding it into Dog's
    virtual int fetch() { return stamina + tricks; }
    virtual Vec pos() { return m_pos; }
    int play();
    int rest();
    int stamina;
    Vec m_pos;
};

class Wing {
public:
    Wing() { span = 1; }
    virtual ~Wing() { span = -1; }
    virtual void flap() { if (span > 0) span--; }
    // Identical to Square::tag: folded at -O2, and the two classes are
    // unrelated, so the one function belongs to neither.
    virtual int tag() { return 7; }
    int span;
};

class Bat : public Animal, public Wing {
public:
    ~Bat() override {}
    int speak() override { return age + echoloc; }
    void flap() override { span += echoloc; }
    int echoloc;
};

class Shape {
public:
    Shape() { sides = 0; }
    virtual ~Shape();
    virtual int area() = 0;
    int sides;
};

Shape::~Shape() { sides = -1; }

class Square : public Shape {
public:
    int area() override { return side * side + sides; }
    virtual int tag() { return 7; }
    int side;
};

class Stats {
public:
    Stats(int seed);
    int bump(int by);
    int total;
    int count;
    long last;
};

class Cat : public virtual Animal {
public:
    ~Cat() override {}
    int speak() override { return age + lives; }
    virtual int kind() { return 3; }
    int lives;
};

}

#ifdef _MSC_VER
#define NOINLINE __declspec(noinline)
#define NOSPEC
#else
#define NOINLINE __attribute__((noinline))
#define NOSPEC __attribute__((optimize("no-devirtualize-speculatively")))
#endif

NOINLINE int zoo::Animal::rate(int k) { return speak() * k + age; }
NOINLINE zoo::Label::Label(int i) : id(i), pad(0), extra(i * 2) {}
// Without NOSPEC -O2 inlines Dog::label under a type guard, and the read of
// Dog::tricks through this would land in Animal.
NOINLINE NOSPEC zoo::Label zoo::Animal::label2() { return label(); }
NOINLINE int zoo::Puppy::play() { return fetch() * 2 + kind(); }
NOINLINE NOSPEC int zoo::Puppy::rest() { return fetch(); }
NOINLINE zoo::Stats::Stats(int seed) : total(seed), count(0), last(-1) {}
NOINLINE int zoo::Stats::bump(int by) { total += by; count++; last = by; return total; }

NOINLINE int use(zoo::Animal* a) { return a->speak() + a->legs(); }
NOINLINE int measure(zoo::Shape* s) { return s->area(); }
NOINLINE void flapit(zoo::Wing* w) { w->flap(); }

namespace zoo {
// A static instance: its constructor stores the vtable into a fixed address
// at startup. No destructor, so the CRT-less MSVC fixture needs no atexit.
class Beacon {
public:
    Beacon() : stats(7) { id = 5; }
    virtual int ping() { return id + stats.total; }
    int id;
    Stats stats;    // an embedded object, built by the constructor at this+16
};
// A namespace-scope free function: Binary Ninja 6.0 types it from the
// mangled name with a bogus zoo* this in front of the real parameters.
NOINLINE int feed(Animal* a, int n) { return a->speak() * n + a->legs(); }

// A namespace function returning a struct by value: it writes through the
// buffer in the first argument register and returns it, the Animal* sits
// in the second.
NOINLINE Vec where(Animal* a, int k) { Vec v; v.x = a->legs() + k; v.y = k; v.z = 0; return v; }

// A class with no evidence but arity: inline constructor, no const member,
// never a parameter type. bump reads a third argument register for its
// two explicit parameters, so it has a hidden this.
class Counter {
    int n = 0;
public:
    NOINLINE int bump(int by, Animal* a) { n += by + a->legs(); return n; }
};
}
zoo::Beacon g_beacon;

// The struct-returning calls live here so main's stack layout around its
// objects stays as it is: the buffers would sit right behind them.
NOINLINE int labels(zoo::Animal* a, zoo::Animal* b, zoo::Puppy* p) {
    zoo::Label lb = a->label();
    zoo::Label lb2 = b->label2();
    zoo::Vec pv = p->pos();
    zoo::Vec w = zoo::where(b, 3);
    return (int)(lb.id + lb2.extra + pv.z + w.x);
}

int main() {
    int r0 = 0;
    zoo::Animal an;
    an.age = 11;
    zoo::Wing w;
    w.span = 2;
    flapit(&w);
    zoo::Dog d;
    d.age = 3;
    d.tricks = 5;
    d.bark();
    zoo::Puppy p;
    p.age = 1;
    p.tricks = 2;
    p.stamina = 8;
    p.m_pos.z = 5;
    zoo::Bat b;
    b.age = 1;
    b.span = 40;
    b.echoloc = 9;
    b.flap();
    zoo::Square sq;
    sq.sides = 4;
    sq.side = 6;
    zoo::Animal* heap = new zoo::Dog;
    heap->age = 7;
    int hs = heap->speak();
    zoo::Cat* cat = new zoo::Cat;
    cat->lives = 9;
    cat->age = 2;
    zoo::Info inf = heap->info();
    zoo::Info inf2 = heap->info2(2, 3);
    r0 = labels(&an, heap, &p);
    int r = r0 + use(&an) + use(&d) + use(&b) + use(heap) + use(cat) + measure(&sq) + w.span + hs + an.describe() + an.rate(3) + heap->rate(2) + g_beacon.ping() + (int)inf.v[3] + (int)inf2.v[1];
    zoo::Stats st(r);
    zoo::Counter ct;
    r += st.bump(2) + st.bump(3) + zoo::feed(&an, 2) + zoo::feed(heap, 3) + p.play() + p.rest() + use(&p) + ct.bump(4, heap);
    delete heap;
    delete cat;
    return r;
}

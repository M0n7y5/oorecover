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

namespace zoo {

// Returned by value: too big for registers, so the caller passes a hidden
// buffer pointer in the first argument register and this moves to the second.
struct Info { long v[5]; };

class Animal {
public:
    Animal() { age = 0; tag = 1; }
    virtual ~Animal() { tag = -1; }
    virtual int speak() { return age; }
    virtual int legs() { return 4; }
    virtual int describe() { return speak() * 100 + legs(); }
    virtual Info info() { Info i; for (int k = 0; k < 5; k++) i.v[k] = age + k; return i; }
    virtual Info info2(int k, long j) { Info i; i.v[0] = age + k; i.v[1] = j; i.v[2] = age + k * j; i.v[3] = k - j; i.v[4] = age - j; return i; }
    int rate(int k);
    int age;
    long tag;
};

class Dog : public Animal {
public:
    ~Dog() override {}
    int speak() override { return age + tricks; }
    virtual void bark() { tricks++; }
    // Identical to Cat::kind: -O2 folds the two into one function that both
    // vtables list; Animal is their common base.
    virtual int kind() { return 3; }
    int tricks;
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
#else
#define NOINLINE __attribute__((noinline))
#endif

NOINLINE int zoo::Animal::rate(int k) { return speak() * k + age; }
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
}
zoo::Beacon g_beacon;

int main() {
    zoo::Animal an;
    an.age = 11;
    zoo::Wing w;
    w.span = 2;
    flapit(&w);
    zoo::Dog d;
    d.age = 3;
    d.tricks = 5;
    d.bark();
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
    int r = use(&an) + use(&d) + use(&b) + use(heap) + use(cat) + measure(&sq) + w.span + hs + an.describe() + an.rate(3) + heap->rate(2) + g_beacon.ping() + (int)inf.v[3] + (int)inf2.v[1];
    zoo::Stats st(r);
    r += st.bump(2) + st.bump(3) + zoo::feed(&an, 2) + zoo::feed(heap, 3);
    delete heap;
    delete cat;
    return r;
}

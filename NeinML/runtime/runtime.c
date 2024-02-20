#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

int64_t print_int(int64_t value) {
    printf("%ld", value);
    return 0;
}

int64_t print_bool(int64_t value) {
    if (value)
        printf("true");
    else
        printf("false");
    return 0;
}

typedef struct {
    int64_t (*fun)();
    int64_t arity;
    int64_t applied_cnt;
    int64_t* applied;
} closure;

#define FREE_CLOSURE(cls) ({\
            free(cls->applied);\
            free(cls);\
        })

int64_t __neinml_alloc_cls(int64_t fun_ptr, int64_t arity)
{
    closure* cls = (closure*) malloc(sizeof(closure));
    cls->fun = (int64_t(*)()) fun_ptr;
    cls->arity = arity;
    cls->applied_cnt = 0;
    cls->applied = (int64_t*) malloc(arity * sizeof(int64_t));

    return (int64_t) cls;
}

int64_t __neinml_apply0(int64_t f_ptr) {
    int64_t(*f)() = (int64_t(*)()) f_ptr;
    return f();
}

static int64_t __neinml_apply1(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0]);
}

static int64_t __neinml_apply2(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1]);
}

static int64_t __neinml_apply3(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2]);
}

static int64_t __neinml_apply4(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2], a[3]);
}

static int64_t __neinml_apply5(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2], a[3], a[4]);
}

static int64_t __neinml_apply6(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2], a[3], a[4], a[5]);
}

static int64_t __neinml_apply7(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2], a[3], a[4], a[5], a[6]);
}

static int64_t __neinml_apply8(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
}

static int64_t __neinml_apply9(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8]);
}

static int64_t __neinml_apply10(closure* cls) {
    int64_t* a = cls->applied;
    return cls->fun(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9]);
}

static int64_t mk_actual_call(closure* clsc) {
    int64_t retval;
    switch (clsc->arity) {
        case 1:
            retval = __neinml_apply1(clsc);
            break;
        case 2:
            retval = __neinml_apply2(clsc);
            break;
        case 3:
            retval = __neinml_apply3(clsc);
            break;
        case 4:
            retval = __neinml_apply4(clsc);
            break;
        case 5:
            retval = __neinml_apply5(clsc);
            break;
        case 6:
            retval = __neinml_apply6(clsc);
            break;
        case 7:
            retval = __neinml_apply7(clsc);
            break;
        case 8:
            retval = __neinml_apply8(clsc);
            break;
        case 9:
            retval = __neinml_apply9(clsc);
            break;
        case 10:
            retval = __neinml_apply10(clsc);
            break;
        default:
            printf("it's not rukaml, so that you must use functions with less than 11 args :(((");
            exit(1);
    }
    FREE_CLOSURE(clsc);
    return retval;
}

int64_t __neinml_applyn(int64_t cls_ptr, int64_t argc, int64_t* argv) {
    closure* cls = (closure*) cls_ptr;
    closure* clsc = (closure*) __neinml_alloc_cls((int64_t) cls->fun, cls->arity);

    for (int i = 0; i < cls->applied_cnt; i++)
        clsc->applied[i] = cls->applied[i];

    int rest = argc > clsc->arity ? clsc->arity - cls->applied_cnt : argc;
    for (int i = 0; i < rest; i++)
        clsc->applied[i + cls->applied_cnt] = argv[i];
    clsc->applied_cnt = rest + cls->applied_cnt;

    if (rest < argc) {
        int64_t retval = mk_actual_call(clsc);
        return __neinml_applyn(retval, argc - rest, argv + rest);
    }

    if (clsc->applied_cnt != clsc->arity)
        return (int64_t) clsc;

    return mk_actual_call(clsc);
}

int64_t __neinml_divide(int64_t a, int64_t b) {
    if (b == 0) {
        printf("Oh no! Your program is trying to divide by 0. So sorry!\n");
        exit(1);
    }
    return a / b;
}

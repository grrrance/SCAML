#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct PartAppl {
    int64_t* fn;
    int tcount; // Total number of arguments
    int acount; // Number of arguments applied
    int64_t* args; // Stored arguments
} *PAply; // Читать как Папли :D

PAply newPaply(int64_t* fn, int tcount) {
    PAply p = (PAply)malloc(sizeof(struct PartAppl));
    p->fn = fn;
    p->tcount = tcount;
    p->acount = 0;
    p->args = (int64_t*)malloc(sizeof(int64_t) * tcount);
    return p;
}

PAply fromPaply(PAply p) {
    PAply p2 = (PAply)malloc(sizeof(struct PartAppl));
    p2->fn = p->fn;
    p2->tcount = p->tcount;
    p2->acount = p->acount;
    p2->args = (int64_t*)malloc(sizeof(int64_t) * p->tcount);
    for (int i = 0; i < p->acount; i++) {
        p2->args[i] = p->args[i];
    }
    return p2;
}

// PAply applyPaply(PAply p, int64_t arg) {
//     if (p->acount < p->tcount){
//         p->args[p->acount] = arg;
//         p->acount++;
//     } else {
//         if (p->acount == p->tcount)
//         {

//         }
        
//     }    
// }
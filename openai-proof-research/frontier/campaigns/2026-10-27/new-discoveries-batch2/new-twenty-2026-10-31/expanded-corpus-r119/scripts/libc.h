// minimal libc prototypes (no system headers available)
#include <stdint.h>
#include <stddef.h>
typedef struct FILE FILE;
int printf(const char*,...); int fprintf(FILE*,const char*,...);
void* calloc(size_t,size_t); void* malloc(size_t); void free(void*); void* memset(void*,int,size_t); void* memcpy(void*,const void*,size_t);
long atol(const char*); int atoi(const char*);
FILE* fopen(const char*,const char*); size_t fwrite(const void*,size_t,size_t,FILE*); size_t fread(void*,size_t,size_t,FILE*); int fclose(FILE*); int fflush(FILE*);
extern FILE* stdout; extern FILE* stderr; void exit(int); void qsort(void*,size_t,size_t,int(*)(const void*,const void*));

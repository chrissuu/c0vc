#include <limits.h>
#include <stdbool.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define C0VC_ARRAY_HEADER_SIZE ((int)sizeof(int64_t))

extern int _c0_main(void);

#ifndef C0VC_NO_MAIN
int main(void) {
  printf("%d\n", _c0_main());
  return 0;
}
#endif

void __c0vc_abort(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(SIGABRT);
  exit(1);
}

void __c0vc_memory_error(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(SIGUSR2);
  exit(1);
}

void __c0vc_arith_error(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(SIGFPE);
  exit(1);
}

void __c0vc_error(void) {
  __c0vc_abort("error statement executed");
}

void __c0vc_assert(bool cond) {
  if (!cond) {
    __c0vc_abort("assertion failed");
  }
}

int __c0vc_checked_div(int lhs, int rhs) {
  if (rhs == 0) {
    __c0vc_arith_error("division by zero");
  }
  if (lhs == INT_MIN && rhs == -1) {
    __c0vc_arith_error("division overflow");
  }
  return lhs / rhs;
}

int __c0vc_checked_mod(int lhs, int rhs) {
  if (rhs == 0) {
    __c0vc_arith_error("modulo by zero");
  }
  if (lhs == INT_MIN && rhs == -1) {
    __c0vc_arith_error("modulo overflow");
  }
  return lhs % rhs;
}

int __c0vc_checked_shr(int lhs, int rhs) {
  if (rhs < 0 || rhs >= 32) {
    __c0vc_arith_error("shift amount out of range");
  }
  return lhs >> rhs;
}

int __c0vc_checked_shl(int lhs, int rhs) {
  if (rhs < 0 || rhs >= 32) {
    __c0vc_arith_error("shift amount out of range");
  }
  return (int)((uint32_t)lhs << rhs);
}

void* __c0vc_alloc(int size) {
  if (size < 0) {
    __c0vc_abort("invalid allocation size");
  }
  size_t bytes = size == 0 ? 1 : (size_t)size;
  void* ptr = calloc(1, bytes);
  if (ptr == NULL) {
    __c0vc_abort("out of memory");
  }
  return ptr;
}

void* __c0vc_alloc_array(int count, int elem_size) {
  if (count < 0) {
    __c0vc_memory_error("negative array allocation size");
  }
  if (elem_size < 0) {
    __c0vc_abort("invalid array allocation size");
  }
  if (elem_size != 0 && count > (INT_MAX - C0VC_ARRAY_HEADER_SIZE) / elem_size) {
    __c0vc_memory_error("array allocation size overflow");
  }
  size_t bytes = (size_t)C0VC_ARRAY_HEADER_SIZE + ((size_t)count * (size_t)elem_size);
  char* raw = (char*)calloc(1, bytes);
  if (raw == NULL) {
    __c0vc_memory_error("out of memory");
  }
  *((int64_t*)raw) = (int64_t)count;
  return raw + C0VC_ARRAY_HEADER_SIZE;
}

void* __c0vc_check_ptr(void* ptr) {
  if (ptr == NULL) {
    __c0vc_memory_error("null pointer dereference");
  }
  return ptr;
}

int __c0vc_array_length(void* arr) {
  if (arr == NULL) {
    __c0vc_memory_error("null array access");
  }
  return (int)(*((int64_t*)((char*)arr - C0VC_ARRAY_HEADER_SIZE)));
}

void* __c0vc_check_array_access(void* arr, int index) {
  int length = __c0vc_array_length(arr);
  if (index < 0 || index >= length) {
    __c0vc_memory_error("array index out of bounds");
  }
  return arr;
}

#ifdef C0VC_WITH_15411_LIB
typedef int c0_float;
typedef void* c0_double;

union float_or_int {
  int as_int;
  float as_float;
};

union double_or_ptr {
  void* as_ptr;
  double as_double;
};

c0_float fadd(c0_float a, c0_float b) {
  union float_or_int x; x.as_int = a;
  union float_or_int y; y.as_int = b;
  union float_or_int z; z.as_float = x.as_float + y.as_float;
  return z.as_int;
}

c0_float fsub(c0_float a, c0_float b) {
  union float_or_int x; x.as_int = a;
  union float_or_int y; y.as_int = b;
  union float_or_int z; z.as_float = x.as_float - y.as_float;
  return z.as_int;
}

c0_float fmul(c0_float a, c0_float b) {
  union float_or_int x; x.as_int = a;
  union float_or_int y; y.as_int = b;
  union float_or_int z; z.as_float = x.as_float * y.as_float;
  return z.as_int;
}

c0_float fdiv(c0_float a, c0_float b) {
  union float_or_int x; x.as_int = a;
  union float_or_int y; y.as_int = b;
  union float_or_int z; z.as_float = x.as_float / y.as_float;
  return z.as_int;
}

bool fless(c0_float a, c0_float b) {
  union float_or_int x; x.as_int = a;
  union float_or_int y; y.as_int = b;
  return x.as_float < y.as_float;
}

c0_float itof(int a) {
  union float_or_int x; x.as_float = (float)a;
  return x.as_int;
}

int ftoi(c0_float a) {
  union float_or_int x; x.as_int = a;
  return (int)x.as_float;
}

c0_double dadd(c0_double a, c0_double b) {
  union double_or_ptr x; x.as_ptr = a;
  union double_or_ptr y; y.as_ptr = b;
  union double_or_ptr z; z.as_double = x.as_double + y.as_double;
  return z.as_ptr;
}

c0_double dsub(c0_double a, c0_double b) {
  union double_or_ptr x; x.as_ptr = a;
  union double_or_ptr y; y.as_ptr = b;
  union double_or_ptr z; z.as_double = x.as_double - y.as_double;
  return z.as_ptr;
}

c0_double dmul(c0_double a, c0_double b) {
  union double_or_ptr x; x.as_ptr = a;
  union double_or_ptr y; y.as_ptr = b;
  union double_or_ptr z; z.as_double = x.as_double * y.as_double;
  return z.as_ptr;
}

c0_double ddiv(c0_double a, c0_double b) {
  union double_or_ptr x; x.as_ptr = a;
  union double_or_ptr y; y.as_ptr = b;
  union double_or_ptr z; z.as_double = x.as_double / y.as_double;
  return z.as_ptr;
}

bool dless(c0_double a, c0_double b) {
  union double_or_ptr x; x.as_ptr = a;
  union double_or_ptr y; y.as_ptr = b;
  return x.as_double < y.as_double;
}

c0_double itod(int a) {
  union double_or_ptr x; x.as_double = (float)a;
  return x.as_ptr;
}

int dtoi(c0_double a) {
  union double_or_ptr x; x.as_ptr = a;
  return (int)x.as_double;
}

void print_dub(c0_double a) {
  union double_or_ptr x; x.as_ptr = a;
  fprintf(stderr, "%g\n", x.as_double);
}

void print_fpt(c0_float a) {
  union float_or_int x; x.as_int = a;
  fprintf(stderr, "%g\n", x.as_float);
}

void print_int(int n) {
  fprintf(stderr, "%d\n", n);
}

void print_hex(int n) {
  fprintf(stderr, "0x%08X\n", n);
}
#endif

#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define C0VC_ARRAY_HEADER_SIZE ((int)sizeof(int64_t))

extern int _c0_main(void);

int main(void) {
  return _c0_main();
}

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

void _c0_assert(int cond) {
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

#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void __c0vc_abort(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(SIGABRT);
  exit(1);
}

void __c0vc_arith_error(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(SIGFPE);
  exit(1);
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
  if (size <= 0) {
    __c0vc_abort("invalid allocation size");
  }
  void* ptr = calloc(1, (size_t)size);
  if (ptr == NULL) {
    __c0vc_abort("out of memory");
  }
  return ptr;
}

void* __c0vc_alloc_array(int count, int elem_size) {
  if (count < 0 || elem_size <= 0) {
    __c0vc_abort("invalid array allocation size");
  }
  if (elem_size != 0 && count > INT_MAX / elem_size) {
    __c0vc_abort("array allocation size overflow");
  }
  void* ptr = calloc((size_t)count, (size_t)elem_size);
  if (ptr == NULL && count != 0) {
    __c0vc_abort("out of memory");
  }
  return ptr;
}

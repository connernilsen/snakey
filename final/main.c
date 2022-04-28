#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include "gc.h"

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t *HEAP, uint64_t size) asm("?our_code_starts_here");
extern void error() asm("?error");
extern SNAKEVAL set_stack_bottom(uint64_t *stack_bottom) asm("?set_stack_bottom");
extern SNAKEVAL print(SNAKEVAL val) asm("?print");
extern SNAKEVAL input(uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t *rsp, uint64_t *rbp, uint64_t args) asm("?print_stack");
extern SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) asm("?equal");
extern uint64_t *try_gc(uint64_t *alloc_ptr, uint64_t amount_needed, uint64_t *first_frame, uint64_t *stack_top) asm("?try_gc");
extern uint64_t *HEAP_END asm("?HEAP_END");
extern uint64_t *HEAP asm("?HEAP");
extern SNAKEVAL tobool(SNAKEVAL val) asm("?tobool");
extern SNAKEVAL tonum(SNAKEVAL val) asm("?tonum");
extern SNAKEVAL tostr(SNAKEVAL val, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?tostr");
extern SNAKEVAL concat(uint64_t *string_1, uint64_t *string_2, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?concat");

const uint64_t NUM_TAG_MASK = 0x0000000000000001;
const uint64_t BOOL_TAG_MASK = 0x000000000000000f;
const uint64_t TUPLE_TAG_MASK = 0x000000000000000f;
const uint64_t CLOSURE_TAG_MASK = 0x000000000000000f;
const uint64_t FORWARD_TAG_MASK = 0x000000000000000f;
const uint64_t STRING_TAG_MASK = 0x000000000000000f;
const uint64_t NUM_TAG = 0x0000000000000000;
const uint64_t BOOL_TAG = 0x000000000000000f;
const uint64_t TUPLE_TAG = 0x0000000000000001;
const uint64_t CLOSURE_TAG = 0x0000000000000005;
const uint64_t FORWARD_TAG = 0x0000000000000003;
const uint64_t STRING_TAG = 0x0000000000000009;
const uint64_t BOOL_TRUE = 0xFFFFFFFFFFFFFFFF;
const uint64_t BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;
const uint64_t NIL = ((uint64_t)NULL | TUPLE_TAG);

const uint64_t ERR_COMP_NOT_NUM = 1;
const uint64_t ERR_ARITH_NOT_NUM = 2;
const uint64_t ERR_NOT_BOOL = 3;
const uint64_t ERR_DESTRUCTURE_INVALID_LEN = 4;
const uint64_t ERR_OVERFLOW = 5;
const uint64_t ERR_GET_NOT_TUPLE = 6;
const uint64_t ERR_GET_LOW_INDEX = 7;
const uint64_t ERR_GET_HIGH_INDEX = 8;
const uint64_t ERR_NIL_DEREF = 9;
const uint64_t ERR_OUT_OF_MEMORY = 10;
const uint64_t ERR_SET_NOT_TUPLE = 11;
const uint64_t ERR_SET_LOW_INDEX = 12;
const uint64_t ERR_SET_HIGH_INDEX = 13;
const uint64_t ERR_CALL_NOT_CLOSURE = 14;
const uint64_t ERR_CALL_ARITY_ERR = 15;
const uint64_t ERR_GET_NOT_NUM = 16;
const uint64_t ERR_NOT_STR = 17;
const uint64_t ERR_INVALID_CONVERSION = 18;

size_t HEAP_SIZE;
uint64_t *STACK_BOTTOM;
uint64_t *HEAP;
uint64_t *HEAP_END;

const int DEBUG_MEM = 0;
const int STRING_SIZE = 100;

SNAKEVAL set_stack_bottom(uint64_t *stack_bottom)
{
  STACK_BOTTOM = stack_bottom;
  return 0;
}

uint64_t *FROM_S;
uint64_t *FROM_E;
uint64_t *TO_S;
uint64_t *TO_E;

SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2)
{
  if (val1 == val2)
  {
    return BOOL_TRUE;
  }
  if (val1 == NIL || val2 == NIL)
  {
    return BOOL_FALSE;
  }
  if ((val1 & TUPLE_TAG_MASK) == TUPLE_TAG && (val2 & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *tup1 = (uint64_t *)(val1 - TUPLE_TAG);
    uint64_t *tup2 = (uint64_t *)(val2 - TUPLE_TAG);
    if (tup1[0] != tup2[0])
    {
      return BOOL_FALSE;
    }
    for (uint64_t i = 1; i <= tup1[0] / 2; i++)
    {
      if (equal(tup1[i], tup2[i]) == BOOL_FALSE)
        return BOOL_FALSE;
    }
    return BOOL_TRUE;
  }
  return BOOL_FALSE;
}

uint64_t tupleCounter = 0;
void printHelp(FILE *out, SNAKEVAL val, int verbose)
{
  if (val == NIL)
  {
    fprintf(out, "nil");
  }
  else if ((val & NUM_TAG_MASK) == NUM_TAG)
  {
    fprintf(out, "%ld", ((int64_t)val) >> 1); // deliberately int64, so that it's signed
  }
  else if (val == BOOL_TRUE)
  {
    fprintf(out, "true");
  }
  else if (val == BOOL_FALSE)
  {
    fprintf(out, "false");
  }
  else if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG)
  {
    uint64_t *addr = (uint64_t *)(val - CLOSURE_TAG);
    fprintf(out, "[%p - 5] ==> <function arity %ld, closed %ld, fn-ptr %p>",
            (uint64_t *)val, addr[0] / 2, addr[1] / 2, (uint64_t *)addr[2]);
    if (verbose)
    {
      fprintf(out, "\nClosed-over values:\n");
      for (uint64_t i = 0; i < addr[1] / 2; i++)
      {
        if (i > 0)
        {
          fprintf(out, "\n");
        }
        if ((addr[3 + i] & TUPLE_TAG_MASK) == 5)
        {
          fprintf(out, "<closure %p>", (uint64_t *)addr[3 + i]);
        }
        else
        {
          printHelp(out, addr[3 + i], verbose);
        }
      }
    }
  }
  else if ((val & TUPLE_TAG_MASK) == 3 && verbose)
  {
    fprintf(out, "forwarding to ");
    fflush(out);
    fprintf(out, "%p", (int *)(val - 3));
    fflush(out);
    return;
  }
  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *addr = (uint64_t *)(val - TUPLE_TAG);
    // Check whether we've visited this tuple already
    if ((*addr & 0x8000000000000000) != 0)
    {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFFFFFFFFFF));
      return;
    }
    if (!(addr >= FROM_S && addr < FROM_E) && !(addr >= TO_S && addr < TO_E) && verbose)
    {
      fprintf(out, "DANGLING POINTER %p", addr);
      return;
    }
    // Mark this tuple: save its length locally, then mark it
    uint64_t len = addr[0];
    if (len & 0x1)
    { // actually, it's a forwarding pointer
      fprintf(out, "forwarding to %p", (uint64_t *)(len - 1));
      return;
    }
    else
    {
      len /= 2; // length is encoded
    }
    // fprintf(out, "Heap is:\n");
    // naive_print_heap(HEAP, HEAP_END);
    // fprintf(out, "%p-->(len=%lu)", (int *)(val - 1), len / 2);
    // fflush(out);
    *(addr) = 0x8000000000000000 | (++tupleCounter);
    fprintf(out, "(");
    for (uint64_t i = 1; i <= len; i++)
    {
      if (i > 1)
        fprintf(out, ", ");
      printHelp(out, addr[i], verbose);
    }
    if (len == 1)
      fprintf(out, ", ");
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len * 2; // length is encoded
  }
  else if ((val & STRING_TAG_MASK) == STRING_TAG)
  {
    uint64_t *addr = (uint64_t *)(val - STRING_TAG);

    if (verbose)
    {
      fprintf(out, "\"");
    }
    int len = ((int)(addr[0])) >> 1;
    for (int i = 0; i < len; i++)
    {
      char c = (char)(addr[i + 1] >> 1);
      fprintf(out, "%c", ((uint8_t *)(addr + 1))[i] >> 1);
    }
    if (verbose)
    {
      fprintf(out, "\"");
    }
  }
  else
  {
    fprintf(out, "Unknown value: %#018lx", val);
  }
}

SNAKEVAL printStack(SNAKEVAL val, uint64_t *rsp, uint64_t *rbp, uint64_t args)
{
  printf("RSP: %#018lx\t==>  ", (uint64_t)rsp);
  fflush(stdout);
  printHelp(stdout, *rsp, 1);
  fflush(stdout);
  printf("\nRBP: %#018lx\t==>  ", (uint64_t)rbp);
  fflush(stdout);
  printHelp(stdout, *rbp, 1);
  fflush(stdout);
  printf("\n(difference: %ld)\n", (uint64_t)(rsp - rbp));
  fflush(stdout);
  printf("Requested return val: %#018lx\t==> ", (uint64_t)val);
  fflush(stdout);
  printHelp(stdout, val, 1);
  fflush(stdout);
  printf("\n");
  fflush(stdout);
  printf("Num args: %ld\n", args);

  uint64_t *origRsp = rsp;

  if (rsp > rbp)
  {
    printf("Error: RSP and RBP are not properly oriented\n");
    fflush(stdout);
  }
  else
  {
    for (uint64_t *cur = rsp; cur < STACK_BOTTOM + 3; cur++)
    {
      if (cur == STACK_BOTTOM)
      {
        printf("BOT %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else if (cur == rbp)
      {
        printf("RBP %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else if (cur == origRsp)
      {
        printf("    %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else if (cur == rbp + 1)
      {
        printf("    %#018lx: %#018lx\t==>  saved ret\n", (uint64_t)cur, *cur);
        fflush(stdout);
        rsp = rbp + 2;
        rbp = (uint64_t *)(*rbp);
      }
      else if (cur == STACK_BOTTOM + 2)
      {
        printf("    %#018lx: %#018lx\t==>  heap\n", (uint64_t)cur, *cur);
        fflush(stdout);
      }
      else
      {
        printf("    %#018lx: %#018lx\t==>  ", (uint64_t)cur, *cur);
        fflush(stdout);
        printHelp(stdout, *cur, 1);
        fflush(stdout);
        printf("\n");
        fflush(stdout);
      }
    }
  }
  return val;
}

uint64_t *reserve_memory(uint64_t *heap_pos, int size, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if (heap_pos + size < HEAP_END)
  {
    return try_gc(heap_pos, size, old_rbp, old_rsp);
  }
  else
  {
    return heap_pos;
  }
}

SNAKEVAL input(uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  char str[STRING_SIZE];
  scanf("%s", str);
  int str_len = 0;
  // TODO: update to handle arbitrary input length
  for (int i = 0; i < STRING_SIZE; i++)
  {
    if (str[i] == 0)
    {
      str_len = i;
      break;
    }
  }
  int byte_length = (str_len + 8 - 1) / 8;
  int space_len = ((byte_length + 2) / 2) * 2;
  uint64_t *ptr = reserve_memory(heap_pos, space_len, old_rbp, old_rsp);
  ptr[0] = str_len * 2;
  for (int i = 0; i < str_len; i++)
  {
    ((uint8_t *)ptr)[i + 8] = (uint8_t)(str[i] << 1);
  }
  return ((uint64_t)ptr) + STRING_TAG;
}

SNAKEVAL concat(uint64_t *string_1, uint64_t *string_2, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  string_1 = (uint64_t *)(((uint64_t)string_1) - STRING_TAG);
  string_2 = (uint64_t *)(((uint64_t)string_2) - STRING_TAG);
  int str1_len = *string_1 >> 1;
  int str2_len = *string_2 >> 1;
  int byte_length = (str1_len + str2_len + 8 - 1) / 8;
  int space_len = ((byte_length + 2) / 2) * 2;

  // string_1 and 2 accessible until here, then seg faults below
  uint64_t *ptr = reserve_memory(heap_pos, space_len, old_rbp, old_rsp);

  *ptr = (str1_len + str2_len) << 1;
  for (int i = 0; i < str1_len; i++)
  {
    ((uint8_t *)ptr)[i + 8] = ((uint8_t *)string_1)[i + 8];
  }
  for (int i = 0; i < str2_len; i++)
  {
    ((uint8_t *)ptr)[i + str1_len + 8] = ((uint8_t *)string_2)[i + 8];
  }
  return ((uint64_t)ptr) + STRING_TAG;
}

SNAKEVAL tobool(SNAKEVAL val)
{
  if ((val & BOOL_TAG_MASK) == BOOL_TAG)
  {
    return val;
  }
  if ((val & NUM_TAG_MASK) == NUM_TAG)
  {
    if (val == 0)
    {
      return BOOL_FALSE;
    }
    else
    {
      return BOOL_TRUE;
    }
  }
  else if ((val & STRING_TAG_MASK) == STRING_TAG)
  {
    uint64_t *addr = (uint64_t *)(val - STRING_TAG);
    uint8_t *b_val;
    int len = ((int)addr[0]) >> 1;
    if (len == 4 || len == 5)
    {
      if (len == 4)
      {
        char t[4] = {'t', 'r', 'u', 'e'};
        b_val = (uint8_t *)t;
      }
      else if (len == 5)
      {
        char f[5] = {'f', 'a', 'l', 's', 'e'};
        b_val = (uint8_t *)f;
      }

      for (int i = 0; i < len; i++)
      {
        if (((((uint8_t *)addr)[i + 8]) >> 1) != b_val[i])
        {
          error(ERR_INVALID_CONVERSION, val);
        }
      }
      if (len == 4)
      {
        return BOOL_TRUE;
      }
      else
      {
        return BOOL_FALSE;
      }
    }
  }
  error(ERR_INVALID_CONVERSION, val);
  return -1;
}

SNAKEVAL tonum(SNAKEVAL val)
{
  if ((val & NUM_TAG_MASK) == NUM_TAG)
  {
    return val;
  }
  else if ((val & STRING_TAG_MASK) == STRING_TAG)
  {
    uint64_t *pre_addr = (uint64_t *)(val - STRING_TAG);
    uint8_t *addr = (uint8_t *)pre_addr;
    int len = ((int)(pre_addr[0])) >> 1;
    int neg = addr[8] == ('-' * 2);
    int offset = 8 + neg;
    len -= neg;
    uint64_t res = 0;
    for (int i = 0; i < len; i++)
    {
      res *= 10;
      char num = addr[i + offset] >> 1;
      if (num < '0' || num > '9')
      {
        error(ERR_INVALID_CONVERSION, val);
      }
      int numval = num - '0';
      res += numval;
    }
    res = res << 1;
    if (neg)
    {
      res *= -1;
    }
    return res;
  }
  else if (val == BOOL_FALSE)
  {
    return 0;
  }
  else if (val == BOOL_TRUE)
  {
    return 2;
  }
  error(ERR_INVALID_CONVERSION, val);
  return -1;
}

SNAKEVAL tostr(SNAKEVAL val, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if ((val & STRING_TAG_MASK) == STRING_TAG)
  {
    // TODO: should this do string copy?
    return val;
  }
  else if ((val & NUM_TAG_MASK) == NUM_TAG)
  {
    int64_t num = (int64_t)(val - NUM_TAG) / 2;
    int neg = num < 0;
    if (neg)
    {
      num *= -1;
    }
    int num_digits = 0;
    if (num == 0)
    {
      num_digits = 1;
    }
    else
    {
      int64_t iter_num = num;
      while (iter_num > 0)
      {
        num_digits += 1;
        iter_num /= 10;
      }
    }
    int byte_length = (num_digits + neg + 8 - 1) / 8;
    int space = ((byte_length + 2) / 2) * 2;
    int offset = 8;
    offset += neg;
    uint64_t *pre_str = reserve_memory(heap_pos, space, old_rbp, old_rsp);
    pre_str[0] = (num_digits + neg) * 2;
    uint8_t *str = (uint8_t *)pre_str;
    if (neg)
    {
      str[8] = (uint8_t)('-' * 2);
    }
    for (int i = 0; i < num_digits; i++)
    {
      int digit = num % 10;
      str[num_digits + offset - i - 1] = (uint64_t)((digit + '0') * 2);
      num = (num - digit) / 10;
    }
    return ((uint64_t)pre_str) + STRING_TAG;
  }
  else if ((val & BOOL_TAG_MASK) == BOOL_TAG)
  {
    uint64_t *pre_str = reserve_memory(heap_pos, 6, old_rbp, old_rsp);
    uint8_t *str = (uint8_t *)pre_str;
    if (val == BOOL_TRUE)
    {
      pre_str[0] = 8;
      str[8] = 't' * 2;
      str[9] = 'r' * 2;
      str[10] = 'u' * 2;
      str[11] = 'e' * 2;
      str[12] = 62;
    }
    else
    {
      pre_str[0] = 10;
      str[8] = 'f' * 2;
      str[9] = 'a' * 2;
      str[10] = 'l' * 2;
      str[11] = 's' * 2;
      str[12] = 'e' * 2;
    }
    return ((uint64_t)pre_str) + STRING_TAG;
  }
  error(ERR_INVALID_CONVERSION, val);
  return -1;
}

SNAKEVAL print(SNAKEVAL val)
{
  printHelp(stdout, val, 0);
  fflush(stdout);
  return val;
}

void error(uint64_t code, SNAKEVAL val)
{
  switch (code)
  {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_NOT_BOOL:
    fprintf(stderr, "Error: expected a boolean, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_DESTRUCTURE_INVALID_LEN:
    fprintf(stderr, "Error: unable to destructure tuple with incorrect length, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_NIL_DEREF:
    fprintf(stderr, "Error: tried to access component of nil\n");
    break;
  case ERR_OUT_OF_MEMORY:
    fprintf(stderr, "Error: out of memory\n");
    break;
  case ERR_SET_NOT_TUPLE:
    fprintf(stderr, "Error: set expected tuple\n");
    break;
  case ERR_SET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to set\n");
    break;
  case ERR_SET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to set\n");
    break;
  case ERR_CALL_NOT_CLOSURE:
    fprintf(stderr, "Error: tried to call a non-closure value: ");
    printHelp(stderr, val, 1);
    break;
  case ERR_CALL_ARITY_ERR:
    fprintf(stderr, "Error: arity mismatch in call\n");
    break;
  case ERR_GET_NOT_NUM:
    fprintf(stderr, "Error: get tuple not number\n");
    break;
  case ERR_NOT_STR:
    fprintf(stderr, "Error: Value not a string, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_INVALID_CONVERSION:
    fprintf(stderr, "Error: conversion function received invalid value, got ");
    printHelp(stderr, val, 1);
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %ld, val: ", code);
    printHelp(stderr, val, 1);
  }
  fprintf(stderr, "\n%p ==> ", (uint64_t *)val);
  printHelp(stderr, val, 1);
  fprintf(stderr, "\n");
  fflush(stderr);
  // naive_print_heap(HEAP, HEAP_END);
  fflush(stdout);
  free(HEAP);
  exit(code);
}

/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does
  not actually allocate the desired number of bytes of memory; the caller
  will do that.

  Arguments:

    uint64_t* alloc_ptr - the current top of the heap (which we store in R15), where
                          the next allocation should occur, if possible
    uint64_t bytes_needed - the number of bytes of memory we want to allocate
                            (including padding)
    uint64_t* cur_frame - the base pointer of the topmost stack frame of our code
                          (i.e., RBP)
    uint64_t* cur_stack_top - the stack pointer of the topmost stack frame of our
                              code (i.e., RSP)

  Returns:
    The new top of the heap (i.e. the new value of R15) after garbage collection.
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP_END to point to the new end of the heap, if it's changed
*/
uint64_t *try_gc(uint64_t *alloc_ptr, uint64_t bytes_needed, uint64_t *cur_frame, uint64_t *cur_stack_top)
{
  uint64_t *new_heap = (uint64_t *)calloc(HEAP_SIZE + 15, sizeof(uint64_t));
  uint64_t *old_heap = HEAP;
  uint64_t *old_heap_end = HEAP_END;

  uint64_t *new_r15 = (uint64_t *)(((uint64_t)new_heap + 15) & ~0xF);
  uint64_t *new_heap_end = new_r15 + HEAP_SIZE;

  FROM_S = (uint64_t *)(((uint64_t)HEAP + 15) & ~0xF);
  FROM_E = HEAP_END;
  TO_S = new_r15;
  TO_E = new_heap_end;

  /* printf("FROM_S = %p, FROM_E = %p, TO_S = %p, TO_E = %p\n", FROM_S, FROM_E, TO_S, TO_E); */
  // naive_print_heap(FROM_S, FROM_E);

  if (DEBUG_MEM)
  {
    smarter_print_heap(FROM_S, FROM_E, TO_S, TO_S);
    printStack(BOOL_TRUE, cur_stack_top, cur_frame, 0);
  }

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL)
  {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection\n");
    fflush(stderr);
    if (old_heap != NULL)
      free(old_heap);
    exit(ERR_OUT_OF_MEMORY);
  }

  new_r15 = gc(STACK_BOTTOM, cur_frame, cur_stack_top, FROM_S, HEAP_END, new_r15);
  HEAP = new_heap;
  HEAP_END = new_heap_end;
  free(old_heap);

  // Note: strict greater-than is correct here: if new_r15 + (bytes_needed / 8) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / sizeof(uint64_t) > HEAP_SIZE)
  {
    fprintf(stderr, "Allocation error: needed %ld words, but the heap is only %ld words\n",
            bytes_needed / sizeof(uint64_t), HEAP_SIZE);
    fflush(stderr);
    if (new_heap != NULL)
    {
      if (DEBUG_MEM)
      {
        smarter_print_heap(FROM_S, FROM_S, TO_S, TO_E);
      }
      free(new_heap);
    }
    exit(ERR_OUT_OF_MEMORY);
  }
  else if ((new_r15 + (bytes_needed / sizeof(uint64_t))) > HEAP_END)
  {
    fprintf(stderr, "Out of memory: needed %ld words, but only %ld remain after collection\n",
            bytes_needed / sizeof(uint64_t), (HEAP_END - new_r15));
    fflush(stderr);
    if (new_heap != NULL)
    {
      if (DEBUG_MEM)
      {
        smarter_print_heap(FROM_S, FROM_S, TO_S, TO_E);
      }
      free(new_heap);
    }
    exit(ERR_OUT_OF_MEMORY);
  }
  else
  {
    /* fprintf(stderr, "new_r15 = %p\n", new_r15); */
    /* naive_print_heap(HEAP, HEAP_END); */
    if (DEBUG_MEM)
    {
      smarter_print_heap(FROM_S, FROM_S, TO_S, TO_E);
    }
    return new_r15;
  }
}

int main(int argc, char **argv)
{
  HEAP_SIZE = 100000;
  if (argc > 1)
  {
    HEAP_SIZE = atoi(argv[1]);
  }
  if (HEAP_SIZE < 0 || HEAP_SIZE > 1000000)
  {
    HEAP_SIZE = 0;
  }
  HEAP = (uint64_t *)calloc(HEAP_SIZE + 15, sizeof(uint64_t));

  uint64_t *aligned = (uint64_t *)(((uint64_t)HEAP + 15) & ~0xF);
  HEAP_END = aligned + HEAP_SIZE;
  /* printf("HEAP = %p, aligned = %p, HEAP_END = %p\n", HEAP, aligned, HEAP_END); */
  SNAKEVAL result = our_code_starts_here(aligned, HEAP_SIZE);
  /* smarter_print_heap(aligned, HEAP_END, TO_S, TO_E); */
  print(result);

  free(HEAP);
  return 0;
}

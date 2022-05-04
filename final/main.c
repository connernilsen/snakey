#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
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
extern SNAKEVAL tostr(SNAKEVAL *val, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?tostr");
extern SNAKEVAL concat(uint64_t *strings_loc, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?concat");
extern SNAKEVAL substr(uint64_t *string, uint64_t start, uint64_t end, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?substr");
extern SNAKEVAL format(uint64_t *values, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?format");
extern SNAKEVAL len(uint64_t val) asm("?len");
extern SNAKEVAL split(uint64_t *args, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?split");
extern SNAKEVAL join(uint64_t *args, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?join");
extern SNAKEVAL tuple(uint64_t value, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?tuple");
extern SNAKEVAL str_to_ascii_tuple(uint64_t *value, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?str_to_ascii_tuple");
extern SNAKEVAL ascii_tuple_to_str(uint64_t *value, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp) asm("?ascii_tuple_to_str");
extern SNAKEVAL get_ascii_char(uint64_t *str, uint64_t off) asm("?get_ascii_char");
extern SNAKEVAL contains(uint64_t *pre_body, uint64_t *pre_val) asm("?contains");

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
const uint64_t ERR_SUBSTRING_NOT_NUM = 19;
const uint64_t ERR_SUBSTRING_OUT_OF_BOUNDS = 20;
const uint64_t ERR_LEN_NOT_TUPLE_NUM = 21;
const uint64_t ERR_INVALID_FORMAT_VALUES = 22;
const uint64_t ERR_INCORRECT_FORMAT_ARITY = 23;
const uint64_t ERR_TUPLE_CREATE_LEN = 24;
const uint64_t ERR_JOIN_NOT_TUPLE = 25;
const uint64_t ERR_JOIN_NOT_STR = 26;
const uint64_t ERR_SPLIT_NOT_STR = 27;
const uint64_t ERR_INVALID_CHAR = 28;

size_t HEAP_SIZE;
uint64_t *STACK_BOTTOM;
uint64_t *HEAP;
uint64_t *HEAP_END;

const int DEBUG_MEM = 0;

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
  if ((val1 & STRING_TAG_MASK) == STRING_TAG && (val2 & STRING_TAG_MASK) == STRING_TAG)
  {
    uint64_t *str1 = (uint64_t *)(val1 - STRING_TAG);
    uint64_t *str2 = (uint64_t *)(val2 - STRING_TAG);
    if (str1[0] != str2[0])
    {
      return BOOL_FALSE;
    }
    int len = (str1[0] + 8 - 1) / 8;
    for (uint64_t i = 1; i <= len; i++)
    {
      if (str1[i] != str2[i])
      {
        return BOOL_FALSE;
      }
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
            (uint64_t *)val, addr[0] / 2, addr[2] / 2, (uint64_t *)addr[1]);
    if (verbose)
    {
      fprintf(out, "\nClosed-over values:\n");
      for (uint64_t i = 0; i < addr[2] / 2; i++)
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
    // if (!(addr >= FROM_S && addr < FROM_E) && !(addr >= TO_S && addr < TO_E) && verbose)
    // {
    //   fprintf(out, "DANGLING POINTER %p", addr);
    //   return;
    // }
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
      printHelp(out, addr[i], 1);
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

/**
 * Reserves memory from within the C runtime. Similar to try_gc, this function
 * will return a heap pointer pointing to the next available location that can store
 * the given amount of data.
 *
 * NOTE: size should be the number of words required, not the number of bytes
 * NOTE: anything that calls this needs to update R15 after returning
 */
uint64_t *reserve_memory(uint64_t *heap_pos, uint64_t size, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if ((uint64_t)(heap_pos + size) >= (uint64_t)HEAP_END)
  {
    return try_gc(heap_pos, size * sizeof(uint64_t), old_rbp, old_rsp);
  }
  else
  {
    return heap_pos;
  }
}

/**
 * Forces a GC pass. Unlike try_gc (which calls this), this function
 * does not try to check the required amount of space and just
 * performs copying/collection immediately.
 */
uint64_t *force_gc(uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
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
    printStack(BOOL_TRUE, old_rsp, old_rbp, 0);
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

  new_r15 = gc(STACK_BOTTOM, old_rbp, old_rsp, FROM_S, HEAP_END, new_r15);
  HEAP = new_heap;
  HEAP_END = new_heap_end;
  free(old_heap);

  return new_r15;
}

/**
 * Get the length of the given value. Only works on strings and tuples.
 */
SNAKEVAL len(uint64_t val)
{
  if ((val & STRING_TAG_MASK) == STRING_TAG)
  {
    return ((uint64_t *)(val - STRING_TAG))[0];
  }
  else if (val == NIL)
  {
    return 0;
  }
  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    return ((uint64_t *)(val - TUPLE_TAG))[0];
  }
  else
  {
    error(ERR_LEN_NOT_TUPLE_NUM, val);
    return -1;
  }
}

/**
 * Reads in an arbitrary length input (assuming enough memory is available) as a string.
 *
 * NOTE: If the read in string is >= 1 - the remaining amount of memory, an oome will
 * be raised
 */
SNAKEVAL input(uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  // force gc immediately to be able to read in as much data into a string as possible
  heap_pos = force_gc(heap_pos, old_rbp, old_rsp);
  // data should be read in at the next heap_pos offset, accounting for the string length value too
  char *str = (char *)(heap_pos + 1);
  // the amount of space available for scanf to read into, accounting for an extra \0 char
  uint64_t available_space = (uint64_t)HEAP_END - (uint64_t)str - 1;
  char fmt_str[30];
  // create a format string that won't write past the end of the heap
  sprintf(fmt_str, "%%%lds", available_space);
  scanf(fmt_str, str);
  uint64_t str_len = 0;
  // keep looping until \0 is reached
  while (str[str_len] != 0)
  {
    // ensure valid char value
    if (str[str_len] > 127)
    {
      char ch = str[str_len] << 1;
      error(ERR_INVALID_CHAR, ch);
    }
    // double char value and update length count
    str[str_len] = str[str_len] << 1;
    str_len++;
  }
  // throw oome if we reached the end of the heap
  if (str_len == available_space)
  {
    error(ERR_OUT_OF_MEMORY, 0);
  }
  // write the length and return
  heap_pos[0] = str_len << 1;
  return ((uint64_t)heap_pos) + STRING_TAG;
}

/**
 * Concat 2 strings.
 *
 * NOTE: Two strings should be passed in as uint64_t**s on the stack, so that
 * they can still be dereferenced after gc.
 */
SNAKEVAL concat(uint64_t *strings_loc, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if ((strings_loc[0] & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_NOT_STR, strings_loc[0]);
  }
  if ((strings_loc[1] & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_NOT_STR, strings_loc[1]);
  }
  // get the strings and their lengths
  uint64_t *str1 = (uint64_t *)(strings_loc[0] - STRING_TAG);
  uint64_t *str2 = (uint64_t *)(strings_loc[1] - STRING_TAG);
  uint64_t str1_len = *str1 >> 1;
  uint64_t str2_len = *str2 >> 1;

  // get the number of bytes and words needed
  uint64_t byte_length = (str1_len + str2_len + 8 - 1) / 8;
  uint64_t space_len = ((byte_length + 2) / 2) * 2;

  uint64_t *ptr = reserve_memory(heap_pos, space_len, old_rbp, old_rsp);

  // re-get the strings, since their locations may have changed during gc
  str1 = (uint64_t *)(strings_loc[0] - STRING_TAG);
  str2 = (uint64_t *)(strings_loc[1] - STRING_TAG);

  // set the resulting length and copy the strings into their destinations
  *ptr = (str1_len + str2_len) << 1;
  for (uint64_t i = 0; i < str1_len; i++)
  {
    ((uint8_t *)ptr)[i + 8] = ((uint8_t *)str1)[i + 8];
  }
  for (uint64_t i = 0; i < str2_len; i++)
  {
    ((uint8_t *)ptr)[i + str1_len + 8] = ((uint8_t *)str2)[i + 8];
  }
  return ((uint64_t)ptr) + STRING_TAG;
}

/**
 * Get the substring of a string given by string_loc, from characters start to finish.
 *
 * NOTE: The string should be passed in as uint64_t**s on the stack, so that
 * it can still be dereferenced after gc.
 */
SNAKEVAL substr(uint64_t *string_loc, uint64_t start, uint64_t finish, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  // get the string location from the stack
  uint64_t *string = (uint64_t *)(string_loc[0] - STRING_TAG);
  // get the lengths and offsets as ints
  uint64_t str_len = *string >> 1;
  start >>= 1;
  finish >>= 1;
  uint64_t new_str_len = finish - start;

  if (start < 0 || start > str_len || finish < start || finish > str_len)
  {
    error(ERR_SUBSTRING_OUT_OF_BOUNDS, string_loc[0]);
  }

  uint64_t byte_length = (new_str_len + 8 - 1) / 8;
  uint64_t space_len = ((byte_length + 2) / 2) * 2;

  uint64_t *ptr = reserve_memory(heap_pos, space_len, old_rbp, old_rsp);
  // re-get the string, since its location may have changed during gc
  string = (uint64_t *)(string_loc[0] - STRING_TAG);

  // set the length and copy the values
  *ptr = new_str_len << 1;
  for (uint64_t i = 0; i < new_str_len; i++)
  {
    ((uint8_t *)ptr)[i + 8] = ((uint8_t *)string)[i + 8 + start];
  }
  return ((uint64_t)ptr) + STRING_TAG;
}

/**
 * Return a formatted string using a format specifier and string values to interpolate in.
 * Values should be a tuple of strings (0 or more), where the first string is a format specifier
 * containing exactly '{}' where values should be interpolated in order.
 * The number of '{}' instances in the format string should match the number of values to interpolate.
 *
 * NOTE: The values should be passed in as uint64_t**s on the stack, so that
 * it can still be dereferenced after gc.
 */
SNAKEVAL format(uint64_t *values, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  // ensure a string is passed in
  if ((*values & TUPLE_TAG_MASK) != TUPLE_TAG)
  {
    error(ERR_INVALID_FORMAT_VALUES, *values);
  }
  // re-get the string tuple, since its location may have changed during gc
  uint64_t *addr = (uint64_t *)(*values - TUPLE_TAG);
  // get the length of format specifier and interpolate values
  uint64_t len = addr[0] >> 1;
  // return with an empty string immediately if there is nothing to interpolate
  if (len == 0)
  {
    uint64_t *res = reserve_memory(heap_pos, 2, old_rbp, old_rsp);
    return ((uint64_t)res) + STRING_TAG;
  }
  // the length of the resulting string (+ 2, since we shouldn't count the fmt str as a substitution)
  uint64_t final_length = 2;
  // loop through the format and substitution strings for length checking and validation
  // starting from 1 to skip the initial tuple length value
  for (uint64_t i = 1; i <= len; i++)
  {
    if ((addr[i] & STRING_TAG_MASK) != STRING_TAG)
    {
      error(ERR_INVALID_FORMAT_VALUES, addr[i]);
    }
    else
    {
      // add the length of this string to the final length, - 2 to account for replacing the
      // '{}' in the format string
      final_length += (((uint64_t *)(addr[i] - STRING_TAG))[0] / 2) - 2;
    }
  }

  // calculate required space and reserve it
  uint64_t byte_length = (final_length + 8 - 1) / 8;
  uint64_t space_len = ((byte_length + 2) / 2) * 2;
  uint64_t *res = reserve_memory(heap_pos, space_len, old_rbp, old_rsp);

  // set the length
  res[0] = (uint64_t)final_length << 1;
  // re-get the tuple, since its location may have changed during gc
  addr = (uint64_t *)(*values - TUPLE_TAG);

  // the current position in the resulting string
  uint64_t curr_pos = 0;
  // the next value to be substituted, starting after the tuple length and format string
  uint64_t curr_subst = 2;
  uint64_t format_str_len = ((uint64_t *)(((uint64_t)addr[1]) - STRING_TAG))[0] / 2;
  uint8_t *format_str = (uint8_t *)((uint64_t)addr[1] - STRING_TAG);
  // loop through and scan each char of the format string, copying values
  for (uint64_t i = 0; i < format_str_len; i++)
  {
    // if a '{}' is encountered, and it's not preceeded by a '\', substitute
    if (format_str[8 + i] / 2 == '{' && i < format_str_len - 1 && format_str[9 + i] / 2 == '}' && (i == 0 || format_str[7 + i] / 2 != '\\'))
    {
      // if there's nothing left to substitute, error
      if (curr_subst > len)
      {
        error(ERR_INCORRECT_FORMAT_ARITY, *values);
      }
      // substitute the next string in and continue
      uint64_t *pre_subst = (uint64_t *)((uint64_t)addr[curr_subst] - STRING_TAG);
      uint64_t subst_len = pre_subst[0] >> 1;
      uint8_t *subst = (uint8_t *)pre_subst;
      for (uint64_t j = 0; j < subst_len; j++)
      {
        ((uint8_t *)res)[curr_pos + 8] = subst[j + 8];
        curr_pos++;
      }
      // move to the next subst item for next time this block is entered
      curr_subst++;
      // increment to skip over the closing }
      i++;
    }
    // otherwise, copy the next character from the format string
    else
    {
      ((uint8_t *)res)[curr_pos + 8] = format_str[i + 8];
      curr_pos++;
    }
  }
  // make sure all subst values were used
  if (curr_subst != len + 1)
  {
    error(ERR_INCORRECT_FORMAT_ARITY, *values);
  }

  return ((uint64_t)res) + STRING_TAG;
}

/**
 * Convert the given value to a bool.
 * - bools are returned immediately
 * - numbers are true if the value is not 0
 * - strings are true if they aren't "false" or empty
 * - tuples are true if they aren't empty
 */
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
    uint64_t len = addr[0] >> 1;
    uint64_t bool_value = 0;
    if (len == 5)
    {
      char f[5] = {'f', 'a', 'l', 's', 'e'};
      uint8_t *b_val = (uint8_t *)f;

      for (uint64_t i = 0; i < len; i++)
      {
        if (((((uint8_t *)addr)[i + 8]) >> 1) != b_val[i])
        {
          bool_value = 1;
          break;
        }
      }
    }
    else if (len != 0)
    {
      bool_value = 1;
    }
    if (bool_value)
    {
      return BOOL_TRUE;
    }
    else
    {
      return BOOL_FALSE;
    }
  }
  else if (val == NIL)
  {
    return BOOL_FALSE;
  }
  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *addr = (uint64_t *)(val - TUPLE_TAG);
    uint64_t len = addr[0] >> 1;
    if (len)
    {
      return BOOL_TRUE;
    }
    else
    {
      return BOOL_FALSE;
    }
  }
  error(ERR_INVALID_CONVERSION, val);
  return -1;
}

/**
 * Convert the given value to a number.
 * - numbers are returned immediately
 * - strings are converted to number values, erroring if they can't be read as a number
 * - bools are 0 if false, 1 if true
 * - other values cannot be converted
 */
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
    uint64_t len = ((int)(pre_addr[0])) >> 1;
    uint64_t neg = addr[8] == ('-' * 2);
    uint64_t offset = 8 + neg;
    len -= neg;
    uint64_t res = 0;
    for (uint64_t i = 0; i < len; i++)
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

/**
 * Converts the given value to a string.
 * - numbers are converted to a string representation of that number
 * - bools are converted to a string representation of "true" or "false"
 * - tuples are converted to "<tuple>", more complex printing should be handled by the user
 * - other values result in an exception
 *
 * NOTE: a string should not be passed in here, the compiled code should
 * determine if the value is a string and return early.
 * NOTE: The value should be passed in as uint64_t**s on the stack, so that
 * it can still be dereferenced after gc.
 */
SNAKEVAL tostr(SNAKEVAL *val, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if ((*val & NUM_TAG_MASK) == NUM_TAG)
  {
    int64_t num = (int64_t)(*val - NUM_TAG) / 2;
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
  else if ((*val & BOOL_TAG_MASK) == BOOL_TAG)
  {
    uint64_t bool_val = *val;
    uint64_t *pre_str = reserve_memory(heap_pos, 6, old_rbp, old_rsp);
    uint8_t *str = (uint8_t *)pre_str;
    if (bool_val == BOOL_TRUE)
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
  else if (*val == NIL)
  {
    uint64_t *str = reserve_memory(heap_pos, 2, old_rbp, old_rsp);
    str[0] = 6;
    ((uint8_t *)str)[8] = 'n' << 1;
    ((uint8_t *)str)[9] = 'i' << 1;
    ((uint8_t *)str)[10] = 'l' << 1;
    return ((uint64_t)str) + STRING_TAG;
  }
  else if ((*val & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *str = reserve_memory(heap_pos, 2, old_rbp, old_rsp);

    str[0] = 14;
    ((uint8_t *)str)[8] = '<' << 1;
    ((uint8_t *)str)[9] = 't' << 1;
    ((uint8_t *)str)[10] = 'u' << 1;
    ((uint8_t *)str)[11] = 'p' << 1;
    ((uint8_t *)str)[12] = 'l' << 1;
    ((uint8_t *)str)[13] = 'e' << 1;
    ((uint8_t *)str)[14] = '>' << 1;
    return ((uint64_t)str) + STRING_TAG;
  }
  error(ERR_INVALID_CONVERSION, *val);
  return -1;
}

/**
 * Creates a tuple of the given length. Each value is initialized to 0.
 *
 * NOTE: The values should be passed in as uint64_t**s on the stack, so that
 * it can still be dereferenced after gc.
 */
SNAKEVAL tuple(uint64_t value, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if ((value & NUM_TAG_MASK) == NUM_TAG && ((int64_t)value) > 0)
  {
    uint64_t space = (((value >> 1) + 2) / 2) * 2;
    uint64_t *tuple = reserve_memory(heap_pos, space, old_rbp, old_rsp);
    tuple[0] = value;
    return ((uint64_t)tuple) + TUPLE_TAG;
  }
  error(ERR_TUPLE_CREATE_LEN, value);
  return -1;
}

/**
 * Converts a tuple containing valid ascii number values to a string.
 * The ascii values must be SNAKEVALS between 0 and 256.

 * NOTE: The value should be passed in as uint64_t**s on the stack, so that
 * it can still be dereferenced after gc.
 */
SNAKEVAL ascii_tuple_to_str(uint64_t *value, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if ((*value & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *addr = (uint64_t *)(*value - TUPLE_TAG);
    uint64_t len = addr[0] >> 1;
    uint64_t byte_length = (len + 8 - 1) / 8;
    uint64_t space = ((byte_length + 2) / 2) * 2;
    uint64_t *str = reserve_memory(heap_pos, space, old_rbp, old_rsp);
    // re-get the tuple, since its location may have changed during gc
    addr = (uint64_t *)(*value - TUPLE_TAG);

    str[0] = addr[0];
    for (uint64_t i = 0; i < len; i++)
    {
      // raise an error if the next value in the tuple isn't a SNAKENUM between 0 and 256
      if ((addr[i + 1] & NUM_TAG_MASK) != NUM_TAG || addr[i + 1] > 255)
      {
        error(ERR_INVALID_CHAR, addr[i + 1]);
      }
      ((uint8_t *)str)[i + 8] = (uint8_t)(addr[i + 1]);
    }
    return ((uint64_t)str) + STRING_TAG;
  }
  error(ERR_INVALID_CONVERSION, *value);
  return -1;
}

/**
 * Converts a string to a tuple containing SNAKENUM ascii values.

 * NOTE: The value should be passed in as uint64_t**s on the stack, so that
 * it can still be dereferenced after gc.
 */
SNAKEVAL str_to_ascii_tuple(uint64_t *value, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  if ((*value & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_INVALID_CONVERSION, *value);
  }
  uint64_t *addr = (uint64_t *)(*value - STRING_TAG);
  uint64_t len = addr[0] >> 1;

  uint64_t space = ((len + 2) / 2) * 2;
  uint64_t *tuple = reserve_memory(heap_pos, space, old_rbp, old_rsp);
  // re-get the string, since its location may have changed during gc
  addr = (uint64_t *)(*value - STRING_TAG);

  tuple[0] = addr[0];
  for (uint64_t i = 0; i < len; i++)
  {
    tuple[i + 1] = (uint64_t)(((uint8_t *)addr)[i + 8]);
  }
  return ((uint64_t)tuple) + TUPLE_TAG;
}

/**
 * Loops through str starting at idx substr until a match for substr is found.
 * Returns the index of the start of the substr in str if a match is found,
 * or BOOL_FALSE otherwise (since it isn't representable as a number in snakeval,
 * so no string can be of length BOOL_FALSE).
 *
 * If the length of substr is 0, then either start_from++ is returned or
 * BOOL_FALSE if start_from == str length - 1.
 */
uint64_t find_next_substr(uint8_t *str, uint8_t *substr, uint64_t start_from)
{
  uint64_t str_len = ((uint64_t *)str)[0] >> 1;
  uint64_t substr_len = ((uint64_t *)substr)[0] >> 1;
  if (substr_len == 0)
  {
    if (start_from >= str_len - 1)
    {
      return BOOL_FALSE;
    }
    else
    {
      return start_from + 1;
    }
  }
  // loop through the main str until the first character of the substring is found,
  // then loop through both to check if it's a match
  // continue on if not until the end of the main str
  for (uint64_t i = start_from; i < str_len; i++)
  {
    if (i + substr_len > str_len)
    {
      break;
    }
    if (str[i + 8] != substr[8])
    {
      continue;
    }
    int found = 0;
    for (uint64_t j = 0; j < substr_len; j++)
    {
      if (str[8 + i + j] != substr[8 + j])
      {
        found = 1;
        break;
      }
    }
    if (!found)
    {
      return i;
    }
  }
  return BOOL_FALSE;
}

uint64_t get_str_words(uint64_t bytes)
{
  uint64_t byte_length = (bytes + 8 - 1) / 8;
  return ((byte_length + 2) / 2) * 2;
}

int align_16(int size)
{
  return ((size + 15) / 16) * 16;
}

SNAKEVAL split(uint64_t *args, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  uint64_t pre_original = args[0];
  uint64_t pre_delim = args[1];
  if ((pre_original & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_SPLIT_NOT_STR, pre_original);
  }
  if ((pre_delim & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_SPLIT_NOT_STR, pre_delim);
  }
  uint8_t *original = (uint8_t *)(pre_original - STRING_TAG);
  uint64_t original_len = ((uint64_t *)(pre_original - STRING_TAG))[0] >> 1;
  uint8_t *delim = (uint8_t *)(pre_delim - STRING_TAG);
  uint64_t delim_len = ((uint64_t *)(pre_delim - STRING_TAG))[0] >> 1;

  uint64_t num_splits = 0;
  uint64_t tot_str_length_words = 0;

  uint64_t pos = 0;
  while (pos < original_len)
  {
    uint64_t next_split = find_next_substr(original, delim, pos);
    if (next_split == BOOL_FALSE)
    {
      next_split = original_len;
    }
    uint64_t split_len = next_split - pos;
    uint64_t space = get_str_words(split_len);

    num_splits++;
    tot_str_length_words += space;
    pos = next_split;
    pos += delim_len;
  }

  uint64_t space = ((num_splits + 2) / 2) * 2;
  space += tot_str_length_words;
  uint64_t *ptr = reserve_memory(heap_pos, space, old_rbp, old_rsp);

  original = (uint8_t *)(args[0] - STRING_TAG);
  delim = (uint8_t *)(args[1] - STRING_TAG);
  uint64_t *res_tuple = ptr + tot_str_length_words;
  res_tuple[0] = num_splits << 1;

  pos = 0;
  for (uint64_t i = 0; i < num_splits; i++)
  {
    uint64_t next_split = find_next_substr(original, delim, pos);
    if (next_split == BOOL_FALSE)
    {
      next_split = original_len;
    }
    uint64_t split_len = next_split - pos;
    ptr[0] = split_len << 1;
    for (uint64_t j = 0; j < split_len; j++)
    {
      ((uint8_t *)ptr)[j + 8] = original[pos + j + 8];
    }

    uint64_t tagged_str = ((uint64_t)ptr) + STRING_TAG;
    res_tuple[i + 1] = tagged_str;
    uint64_t space = get_str_words(split_len);
    ptr += space;
    pos = next_split;
    pos += delim_len;
  }

  return ((uint64_t)res_tuple) + TUPLE_TAG;
}

SNAKEVAL join(uint64_t *args, uint64_t *heap_pos, uint64_t *old_rbp, uint64_t *old_rsp)
{
  uint64_t strs = args[0];
  uint64_t delim = args[1];
  if ((strs & TUPLE_TAG_MASK) != TUPLE_TAG)
  {
    error(ERR_JOIN_NOT_TUPLE, strs);
  }
  if ((delim & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_JOIN_NOT_STR, delim);
  }
  uint64_t *strs_untagged = (uint64_t *)(strs - TUPLE_TAG);
  uint64_t strs_len = strs_untagged[0] >> 1;
  uint64_t *delim_untagged = (uint64_t *)(delim - STRING_TAG);
  uint64_t delim_len = delim_untagged[0] >> 1;

  int length = 0;
  // calculate length
  for (int i = 1; i <= strs_len; i++)
  {
    uint64_t str_tagged = strs_untagged[i];
    if ((((uint64_t)str_tagged) & STRING_TAG_MASK) != STRING_TAG)
    {
      error(ERR_JOIN_NOT_STR, delim);
    }
    uint64_t *str_untagged = (uint64_t *)(str_tagged - STRING_TAG);
    length += str_untagged[0] >> 1;
  }
  if (strs_len > 1)
  {
    length += delim_len * (strs_len - 1);
  }

  // add space for length
  int space = align_16(length + 8);
  uint64_t *result_str = reserve_memory(heap_pos, space, old_rbp, old_rsp);

  result_str[0] = length << 1;
  // characters of strs we have already placed in string
  int str_chars = 0;
  while (str_chars < length)
  {
    for (int i = 1; i <= strs_len; i++)
    {
      uint64_t *str_untagged = (uint64_t *)(strs_untagged[i] - STRING_TAG);
      int str_len = str_untagged[0] >> 1;
      // while we still have chars from this string to copy...
      int str_len_idx = 0;
      while (str_chars < length && str_len_idx < str_len)
      {
        ((uint8_t *)result_str)[8 + str_chars] = ((uint8_t *)str_untagged)[8 + str_len_idx];
        str_chars++;
        str_len_idx++;
      }
      if (str_chars < length)
      {
        for (int i = 0; i < delim_len; i++)
        {
          ((uint8_t *)result_str)[8 + str_chars] = ((uint8_t *)delim_untagged)[8 + i];
          str_chars++;
        }
      }
    }
  }
  return ((uint64_t)result_str) + STRING_TAG;
}

/**
 * Determine if the given string contains the given substring.
 * Returns true if so, false otherwise.
 */
SNAKEVAL contains(uint64_t *pre_body, uint64_t *pre_val)
{
  if (((uint64_t)pre_body & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_NOT_STR, pre_body);
  }
  if (((uint64_t)pre_val & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_NOT_STR, pre_val);
  }
  uint64_t val_len = ((uint64_t *)(((uint64_t)pre_val) - STRING_TAG))[0] >> 1;
  uint8_t *body = (uint8_t *)((uint64_t)pre_body - STRING_TAG);
  uint8_t *val = (uint8_t *)((uint64_t)pre_val - STRING_TAG);

  // if the substr is empty, short circuit
  if (val_len == 0)
  {
    return BOOL_TRUE;
  }

  if (find_next_substr(body, val, 0) != BOOL_FALSE)
  {
    return BOOL_TRUE;
  }
  else
  {
    return BOOL_FALSE;
  }
}

/**
 * Get the SNAKENUM ascii representation of the character at the
 * given offset of the given string.
 */
SNAKEVAL get_ascii_char(uint64_t *str, uint64_t offset)
{
  if (((uint64_t)str & STRING_TAG_MASK) != STRING_TAG)
  {
    error(ERR_NOT_STR, str);
  }
  if ((offset & NUM_TAG_MASK) != NUM_TAG)
  {
    error(ERR_SUBSTRING_NOT_NUM, offset);
  }
  if (((int64_t)offset) < 0)
  {
    error(ERR_GET_LOW_INDEX, offset);
  }
  uint64_t *addr = (uint64_t *)((uint64_t)str - STRING_TAG);
  if (offset >= addr[0])
  {
    error(ERR_GET_HIGH_INDEX, offset);
  }
  return ((uint8_t *)addr)[(offset >> 1) + 8];
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
  case ERR_SUBSTRING_NOT_NUM:
    fprintf(stderr, "Error: substring expected num, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_SUBSTRING_OUT_OF_BOUNDS:
    fprintf(stderr, "Error: substring index out of bounds of string ");
    printHelp(stderr, val, 1);
    break;
  case ERR_LEN_NOT_TUPLE_NUM:
    fprintf(stderr, "Error: len expected tuple or num, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_JOIN_NOT_TUPLE:
    fprintf(stderr, "Error: unable to join non-tuple ");
    printHelp(stderr, val, 1);
    break;
  case ERR_JOIN_NOT_STR:
    fprintf(stderr, "Error: unable to join non-string ");
    printHelp(stderr, val, 1);
    break;
  case ERR_SPLIT_NOT_STR:
    fprintf(stderr, "Error: unable to split non-string ");
    printHelp(stderr, val, 1);
    break;
  case ERR_INVALID_FORMAT_VALUES:
    fprintf(stderr, "Error: incorrect value types for format, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_INCORRECT_FORMAT_ARITY:
    fprintf(stderr, "Error: incorrect arity for format replacement values, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_TUPLE_CREATE_LEN:
    fprintf(stderr, "Tuple creation expected num, got ");
    printHelp(stderr, val, 1);
    break;
  case ERR_INVALID_CHAR:
    fprintf(stderr, "Given char ascii value is invalid, got ");
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
  uint64_t *new_r15 = force_gc(alloc_ptr, cur_frame, cur_stack_top);

  // Note: strict greater-than is correct here: if new_r15 + (bytes_needed / 8) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / sizeof(uint64_t) > HEAP_SIZE)
  {
    fprintf(stderr, "Allocation error: needed %ld words, but the heap is only %ld words\n",
            bytes_needed / sizeof(uint64_t), HEAP_SIZE);
    fflush(stderr);
    if (HEAP != NULL)
    {
      if (DEBUG_MEM)
      {
        smarter_print_heap(FROM_S, FROM_S, TO_S, TO_E);
      }
      free(HEAP);
    }
    exit(ERR_OUT_OF_MEMORY);
  }
  else if ((new_r15 + (bytes_needed / sizeof(uint64_t))) > HEAP_END)
  {
    fprintf(stderr, "Out of memory: needed %ld words, but only %ld remain after collection\n",
            bytes_needed / sizeof(uint64_t), (HEAP_END - new_r15));
    fflush(stderr);
    if (HEAP != NULL)
    {
      if (DEBUG_MEM)
      {
        smarter_print_heap(FROM_S, FROM_S, TO_S, TO_E);
      }
      free(HEAP);
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

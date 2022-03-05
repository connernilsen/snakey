#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t *HEAP, int size) asm("our_code_starts_here");
extern void error(uint64_t code, SNAKEVAL val) asm("error");
extern SNAKEVAL print(SNAKEVAL val) asm("print");
extern SNAKEVAL input() asm("input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t *esp, uint64_t *ebp, int args) asm("print_stack");
extern uint64_t *STACK_BOTTOM asm("STACK_BOTTOM");

uint64_t *HEAP;

const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t TAG_MASK = 0x0000000000000007L;
const uint64_t BOOL_TAG = 0x0000000000000007L;
const uint64_t TUPLE_TAG = 0x0000000000000001L;
const uint64_t TRUE = 0xFFFFFFFFFFFFFFFFL;
const uint64_t FALSE = 0x7FFFFFFFFFFFFFFFL;
const uint64_t COMP_NOT_NUM = 1L;
const uint64_t ARITH_NOT_NUM = 2L;
const uint64_t NOT_BOOL = 3L;
const uint64_t OVERFLOW = 4L;

const int UNKNOWN_TYPE = 0;
const int NUM_TYPE = 1;
const int BOOL_TYPE = 2;
const int TUPLE_TYPE = 3;

/**
 * Determine the type of the given value by comparing the tags
 * with known type tags and return a representative type constant.
 */
int getValueType(SNAKEVAL val)
{
  if ((NUM_TAG_MASK & val) == 0L)
  {
    return NUM_TYPE;
  }
  else if ((TAG_MASK & val) == BOOL_TAG)
  {
    return BOOL_TYPE;
  }
  else if ((TAG_MASK & val) == TUPLE_TAG)
  {
    return TUPLE_TYPE;
  }
  else
  {
    return UNKNOWN_TYPE;
  }
}

/**
 * Converts the given type constant to a string
 * describing the type (e.g. number type -> num)
 *
 * NOTE: caller needs to free returned value's memory, since it's
 * returned as a char array.
 */
char *convertTypeToStr(int type)
{
  switch (type)
  {
  case NUM_TYPE:
    return strdup("num");
    break;
  case BOOL_TYPE:
    return strdup("bool");
    break;
  case TUPLE_TYPE:
    return strdup("tuple");
    break;
  default:
    return strdup("unknown");
  }
}

/**
 * Converts the given value to a string representing the value.
 *
 * If debug evaluates to true, then the returned
 * value is returned as "<type>(<value_as_str>)".
 *
 * NOTE: caller needs to free returned value
 */
char *convertValueToStr(SNAKEVAL val, char debug)
{
  int valType = getValueType(val);
  char valueStr[21];
  // convert val to a string
  switch (valType)
  {
  case NUM_TYPE:
    sprintf(valueStr, "%ld", ((int64_t)val) >> 1);
    break;
  case BOOL_TYPE:
    if (val == TRUE)
    {
      strcpy(valueStr, "true");
    }
    else if (val == FALSE)
    {
      strcpy(valueStr, "false");
    }
    else
    {
      sprintf(valueStr, "%#018lx", val);
    }
    break;
  case TUPLE_TYPE:
  {
    int64_t *vals = (int64_t *)(val ^ TUPLE_TAG);
    strcpy(valueStr, "(");
    for (int i = 1; i < vals[0] + 1; i++)
    {
      char* next = convertValueToStr(vals[i], debug);
      strcat(valueStr, next);
      if (i != vals[0]) {
        strcat(valueStr, ", ");
      }
      free(next);
    }
    strcat(valueStr, ")");
    break;
  }
  default:
    sprintf(valueStr, "%#018lx", val);
  }
  // return immediately if not debug
  if (!debug)
  {
    return strdup(valueStr);
  }
  // convert the type to a string and format as <type>(<value>)
  char *typeStr = convertTypeToStr(valType);
  char result[50];
  sprintf(result, "%s(%s)", typeStr, valueStr);

  // free the typeStr memory
  free(typeStr);
  return strdup(result);
}

/**
 * Handle an error. The print statement depends
 * on the error code given.
 *
 * The value is converted to a string if possible
 * with debug == true using convertValueToStr.
 *
 * After the error message is printed, exit(errCode) is called.
 */
void error(uint64_t errCode, uint64_t val)
{
  char *valueStr = convertValueToStr(val, 1);

  if (errCode == COMP_NOT_NUM)
  {
    fprintf(stderr,
            "comparison expected a number, got %s\n", valueStr);
  }
  else if (errCode == ARITH_NOT_NUM)
  {
    fprintf(stderr,
            "arithmetic expected a number, got %s\n", valueStr);
  }
  else if (errCode == NOT_BOOL)
  {
    fprintf(stderr,
            "expected a boolean, got %s\n", valueStr);
  }
  // todo: not tuple
  else if (errCode == OVERFLOW)
  {
    fprintf(stderr,
            "overflow occurred for arithmetic operation, got %s\n", valueStr);
  }
  else
  {
    fprintf(stderr,
            "unknown error code provided (%#018lx) for value %s\n",
            errCode, valueStr);
  }

  free(valueStr);
  exit(errCode);
}

SNAKEVAL print(SNAKEVAL val)
{
  char *valueStr = convertValueToStr(val, 0);
  printf("%s\n", valueStr);
  free(valueStr);
  return val;
}

// main should remain unchanged
// You can pass in a numeric argument to your program when you run it,
// to specify the size of the available heap.  You may find this useful
// for debugging...
int main(int argc, char **argv)
{
  int size = 100000;
  if (argc > 1)
  {
    size = atoi(argv[1]);
  }
  if (size < 0 || size > 1000000)
  {
    size = 0;
  }
  HEAP = calloc(size, sizeof(int));

  SNAKEVAL result = our_code_starts_here(HEAP, size);
  print(result);
  free(HEAP);
  return 0;
}

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t *HEAP, int size) asm("our_code_starts_here");
extern void error(uint64_t code, SNAKEVAL val) asm("error");
extern SNAKEVAL print(SNAKEVAL val) asm("print");
extern SNAKEVAL input() asm("input");
extern SNAKEVAL equal(SNAKEVAL v1, SNAKEVAL v2) asm("equal");
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
const uint64_t GET_NOT_TUPLE = 5L;
const uint64_t GET_LOW_INDEX = 6L;
const uint64_t GET_HIGH_INDEX = 7L;
const uint64_t NIL_DEREF = 8L;
const uint64_t GET_NOT_NUM = 9L;
const uint64_t DESTRUCTURE_INVALID_LEN = 10L;

const uint64_t MAX_VAL_LENGTH = 500;
const int CYCLE_ARR_LENGTH = 50;

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

int findPosInList(uint64_t **list, uint64_t *val) {
  for (int i = 0; i < CYCLE_ARR_LENGTH; i++)
  {
    if (list[i] == val)
    {
      return i;
    }
  }
  return -1;
}

/**
 * Converts the given value to a string representing the value.
 *
 * If debug evaluates to true, then the returned
 * value is returned as "<type>(<value_as_str>)".
 *
 * NOTE: caller needs to free returned value
 */
char *convertValueToStr(SNAKEVAL val, char debug, uint64_t **seen, int idx)
{
  int valType = getValueType(val);
  char valueStr[MAX_VAL_LENGTH];
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
    if (val == TUPLE_TAG) {
      return strdup("nil");
    }
    uint64_t *vals = (uint64_t *)(val ^ TUPLE_TAG);
    int assocListPos = findPosInList(seen, vals);
    if (assocListPos > -1) {
      char message[20];
      sprintf(message, "<cyclic tuple %d>", assocListPos + 1);
      strcpy(valueStr, message);
      break;
    }
    seen[idx] = vals;
    idx++;
    int length = vals[0];
    strcpy(valueStr, "(");
    for (int i = 1; i < length + 1; i++)
    {
      char* next = convertValueToStr(vals[i], debug, seen, idx);
      strcat(valueStr, next);
      if (i != length) {
        strcat(valueStr, ", ");
      }
      else if (length == 1) {
        strcat(valueStr, ",");
      }
      free(next);
    }
    strcat(valueStr, ")");
    if (idx > 0) {
      seen[idx - 1] = 0L;
    }
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

SNAKEVAL convertStrToVal(char *str) {
  if (strcmp("true", str) == 0) {
    return TRUE;
  }
  else if (strcmp("false", str) == 0)
  {
    return FALSE;
  }
  else {
    return atoi(str) << 1;
  }
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
  uint64_t *arr[CYCLE_ARR_LENGTH];
  char *valueStr = convertValueToStr(val, 1, arr, 0);

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
  else if (errCode == GET_NOT_TUPLE) {
    fprintf(stderr, "tuple access expected tuple %s\n", valueStr);
  }
  else if (errCode == GET_LOW_INDEX)
  {
    fprintf(stderr, "unable to access index of tuple %s, length %ld. index too small\n", valueStr, ((int64_t*)(val ^ TUPLE_TAG))[0]);
  }
  else if (errCode == GET_HIGH_INDEX)
  {
    fprintf(stderr, "unable to access index of tuple %s, length %ld. index too large\n", valueStr, ((int64_t *) (val ^ TUPLE_TAG))[0]);
  }
  else if (errCode == GET_NOT_NUM)
  {
    fprintf(stderr, "unable to access tuple position %s\n", valueStr);
  }
  else if (errCode == OVERFLOW)
  {
    fprintf(stderr,
            "overflow occurred for arithmetic operation, got %s\n", valueStr);
  }
  else if (errCode == NIL_DEREF) 
  {
    fprintf(stderr, "unable to dereference value, got %s\n", valueStr);
  }
  else if (errCode == DESTRUCTURE_INVALID_LEN)
  {
    fprintf(stderr, "unable to destructure tuple with incorrect length %s\n", valueStr);
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
  uint64_t *arr[CYCLE_ARR_LENGTH];
  char *valueStr = convertValueToStr(val, 0, arr, 0);
  printf("%s\n", valueStr);
  free(valueStr);
  return val;
}

SNAKEVAL input()
{
  char str[100];
  scanf("%s", str);
  return convertStrToVal(str);
}

// Structural equality for snakevals
SNAKEVAL equal(SNAKEVAL v1, SNAKEVAL v2) {
  uint64_t **arr = calloc(CYCLE_ARR_LENGTH, sizeof(uint64_t *));
  uint64_t **arr2 = calloc(CYCLE_ARR_LENGTH, sizeof(uint64_t *));
  // free
  uint64_t res;
  if (strcmp(convertValueToStr(v1, 0, arr, 0), convertValueToStr(v2, 0, arr2, 0)) == 0) {
    res = TRUE;
  } else {
    res = FALSE;
  }
  free(arr);
  free(arr2);
  return res;
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

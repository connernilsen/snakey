#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");
extern void error(uint64_t errCode, uint64_t val) asm("error");

const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t TRUE = 0xFFFFFFFFFFFFFFFFL;
const uint64_t FALSE = 0x7FFFFFFFFFFFFFFFL;
const uint64_t COMP_NOT_NUM = 1L;
const uint64_t ARITH_NOT_NUM = 2L;
const uint64_t LOGIC_NOT_BOOL = 3L;
const uint64_t IF_NOT_BOOL = 4L;
const uint64_t OVERFLOW = 5L;

const int UNKNOWN_TYPE = 0;
const int NUM_TYPE = 1;
const int BOOL_TYPE = 2;

int getValueType(uint64_t val) {
  /* if (((NUM_TAG_MASK ^ val) & 1) == 1) { */
  if ((NUM_TAG_MASK & val) == 0L) {
    return NUM_TYPE;
  }
  else if ((BOOL_TAG_MASK & val) == BOOL_TAG_MASK) {
    return BOOL_TYPE;
  }
  else {
    return UNKNOWN_TYPE;
  }
}

// NOTE: caller needs to free returned value
char* convertTypeToStr(int type) {
  switch (type) {
    case NUM_TYPE:
      return strdup("num");
      break;
    case BOOL_TYPE:
      return strdup("bool");
      break;
    default:
      return strdup("unknown");
  }
}

// NOTE: caller needs to free returned value
char* convertValueToStr(uint64_t val, char debug) {
  int valType = getValueType(val);
  char valueStr[21];
  switch (valType) {
    case NUM_TYPE:
      sprintf(valueStr, "%lu", val >> 1);
      break;
    case BOOL_TYPE:
      if (val == TRUE) {
        strcpy(valueStr, "true");
      }
      else if (val == FALSE) {
        strcpy(valueStr, "false");
      } else {
        sprintf(valueStr, "%#018lx", val);
      }
      break;
    default:
      sprintf(valueStr, "%#018lx", val);
  }

  if (!debug) {
    return strdup(valueStr);
  }

  char* typeStr = convertTypeToStr(valType);
  char result[50];
  sprintf(result, "%s(%s)", typeStr, valueStr);

  free(typeStr);
  return strdup(result);
}

void error(uint64_t errCode, uint64_t val) {
  char* valueStr = convertValueToStr(val, 1);

  if (errCode == COMP_NOT_NUM) {
    fprintf(stderr, 
      "comparison expected a number, got %s\n", valueStr);
  } else if (errCode == ARITH_NOT_NUM) {
    fprintf(stderr, 
      "arithmetic expected a number, got %s\n", valueStr);
  } else if (errCode == LOGIC_NOT_BOOL) {
    fprintf(stderr, 
      "logic expected a boolean, got %s\n", valueStr);
  } else if (errCode == IF_NOT_BOOL) {
    fprintf(stderr, 
      "if expected a boolean, got %s\n", valueStr);
  } else if (errCode == OVERFLOW) {
    fprintf(stderr, 
      "overflow occurred for arithmetic operation, got %s\n", valueStr);
  } else {
    fprintf(stderr, 
      "unknown error code provided (%#018lx) for value %s\n", 
      errCode, valueStr);
  }

  free(valueStr);
  exit(errCode);
}

uint64_t print(uint64_t val) {
  char* valueStr = convertValueToStr(val, 0);
  printf("%s\n", valueStr);
  free(valueStr);
  return val;
}

int main(int argc, char **argv)
{
  uint64_t result = our_code_starts_here();
  print(result);
  return 0;
}

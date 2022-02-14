#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");
extern void error(int errCode, int val) asm("error");
const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t TRUE = 0xFFFFFFFFFFFFFFFFL;
const uint64_t FALSE = 0x7FFFFFFFFFFFFFFFL;
const int COMP_NOT_NUM = 1;
const int ARITH_NOT_NUM = 2;
const int LOGIC_NOT_BOOL = 3;
const int IF_NOT_BOOL = 4;
const int OVERFLOW = 5;

void error(int errCode, int val) {
  if (errCode == COMP_NOT_NUM) {
    fprintf(stderr, "Expected number type for comparison op, got %010x\n", val);
  } else if (errCode == ARITH_NOT_NUM) {
    fprintf(stderr, "Expected number type for arithmetic op, got %010x\n", val);
  } else if (errCode == LOGIC_NOT_BOOL) {
    fprintf(stderr, "Expected bool type for logical op, got %010x\n", val);
  } else if (errCode == IF_NOT_BOOL) {
    fprintf(stderr, "Expected bool type for if stmt, got %010x\n", val);
  } else if (errCode == OVERFLOW) {
    fprintf(stderr, "Overflow occurred for arithmetic operation, got %010x\n", val);
  } else {
    fprintf(stderr, "Unknown error code provided (%d) for value %010x\n", 
        errCode, val);
  }

  exit(errCode);
}

uint64_t print(uint64_t val)
{
  // TODO: handle errors too
  // Number
  if (((NUM_TAG_MASK ^ val) & 1) == 1)
  {
    printf("%lu", val >> 1); // maybe llu/lld/ld?
  }
  else if (val == TRUE)
  {
    printf("true");
  }
  else if (val == FALSE)
  {
    printf("false");
  }
  else if (((BOOL_TAG_MASK ^ val) & 1) == 1)
  {
    printf("Bool tag provided with hex value: %#018lx\n", val);
  }
  else
  {
    printf("Unknown value and type: %#018lx\n", val);
  }

  return val;
}

int main(int argc, char **argv)
{
  uint64_t result = our_code_starts_here();
  print(result);
  return 0;
}

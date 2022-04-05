#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef uint64_t SNAKEVAL;

void printHelp(FILE *out, SNAKEVAL val);
extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t FORWARD_TAG_MASK;
extern uint64_t CLOSURE_TAG;
extern uint64_t FORWARD_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t NIL;
extern uint64_t tupleCounter;
extern uint64_t *STACK_BOTTOM;
extern uint64_t *FROM_S;
extern uint64_t *FROM_E;
extern uint64_t *TO_S;
extern uint64_t *TO_E;

const uint64_t FILLER = 63;

void naive_print_heap(uint64_t *heap, uint64_t *heap_end)
{
  printf("In naive_print_heap from %p to %p\n", heap, heap_end);
  for (uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1)
  {
    printf("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t *)(*(heap + i)), *(heap + i));
  }
}

// Implement the functions below

void smarter_print_heap(uint64_t *from_start, uint64_t *from_end, uint64_t *to_start, uint64_t *to_end)
{
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible
  exit(1);
}

/**
 * Return the number of memory slots needed, possibly with padding.
 *
 * Arguments:
 *  slots: the number of un-padded slots in memory required
 */
int get_padded_slots(int slots)
{
  return (((slots + 1) / 2) * 2);
}

/**
 * Replace an object in the old semispace with a forward and filler.
 *
 * Arguments:
 *  start: the address of the value in the old semispace
 *  new_addr: the address of the value in the new semispace
 *  length: the padded length of the object in memory
 *
 * Side effects:
 *  Replaces the initial value in memory with the tagged forwarding address,
 *  and any following values for the rest of the length with FILLER.
 *  E.g.: [ tagged fwd addr | 63 | 63 | 63 | ... ]
 */
void replace_with_forward(uint64_t *start, uint64_t *new_addr, int length)
{
  start[0] = (uint64_t *)((uint64_t)new_addr + FORWARD_TAG);
  for (int i = 1; i < length; i++)
  {
    start[i] = FILLER;
  }
}

/*
  Copies a Garter value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location
    with a forwarding pointer to its new location
 */
uint64_t *copy_if_needed(uint64_t *val_addr, uint64_t *heap_top)
{
  // get the tag of the value in the stack/heap location
  // and exit if it's not a closure or tuple
  uint64_t top_level_val = *val_addr;
  uint64_t tag = top_level_val & FORWARD_TAG_MASK;
  if (tag != CLOSURE_TAG && tag != TUPLE_TAG)
  {
    return heap_top;
  }

  uint64_t *memory_addr = (uint64_t *)(top_level_val - tag);

  if (((*memory_addr) & FORWARD_TAG_MASK) == FORWARD_TAG)
  {
    uint64_t forwarded_addr = (*memory_addr) - FORWARD_TAG;
    uint64_t *tagged_addr = (uint64_t *)(forwarded_addr + tag);
    *val_addr = tagged_addr;
    return heap_top;
  }

  int metadata_length;
  uint64_t length_raw;
  if (tag == CLOSURE_TAG)
  {
    heap_top[0] = memory_addr[0];
    heap_top[1] = memory_addr[1];
    uint64_t length_raw = memory_addr[2];
    heap_top[2] = length_raw;

    int metadata_length = 3;
  }
  else
  {
    uint64_t length_raw = memory_addr[0];
    heap_top[0] = length_raw;

    int metadata_length = 1;
  }

  int length = ((int)length_raw) / 2;

  int slots = get_padded_slots(length + metadata_length);

  for (int i = 0; i < length; i++)
  {
    heap_top[metadata_length + i] = memory_addr[metadata_length + i];
  }

  replace_with_forward(memory_addr, heap_top, slots);

  *val_addr = (uint64_t *)((uint64_t)heap_top + tag);

  return heap_top + slots;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t *gc(uint64_t *bottom_frame, uint64_t *top_frame, uint64_t *top_stack, uint64_t *from_start, uint64_t *from_end, uint64_t *to_start)
{
  uint64_t *to_start_origin = to_start;
  uint64_t *old_top_frame = top_frame;
  do
  {
    for (uint64_t *cur_word = top_stack /* maybe need a +1 here? */; cur_word < top_frame; cur_word++)
    {
      to_start = copy_if_needed(cur_word, to_start);
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack frame,
     * [top_frame + 8] is the return address, and
     * [top_frame + 16] is therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t *)(*top_frame);
  } while (old_top_frame < bottom_frame); // Use the old stack frame to decide if there's more GC'ing to do

  do
  {
    uint64_t tag = ((uint64_t)to_start_origin) & FORWARD_TAG_MASK;
    int length, metadata_offset;
    uint64_t *heap_addr = (uint64_t *)((uint64_t)to_start_origin - tag);
    if (tag == CLOSURE_TAG)
    {
      metadata_offset = 3;
      length = ((int)heap_addr[2]) / 2;
    }
    else if (tag == TUPLE_TAG)
    {
      metadata_offset = 1;
      length = ((int)heap_addr[0]) / 2;
    }
    else
    {
      fprintf(stderr, "Got unexpected tag type: %ld", tag);
      exit(17);
    }

    int slots = get_padded_slots(metadata_offset + length);
    for (int i = metadata_offset; i < length; i++)
    {
      to_start = copy_if_needed(heap_addr + i, to_start);
    }
    to_start_origin += slots;
  } while (to_start_origin < to_start);

  // after copying and GC'ing all the stack frames, return the new allocation starting point
  return to_start;
}

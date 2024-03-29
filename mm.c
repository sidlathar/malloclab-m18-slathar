/* SIDDHANTH LATHAR SLATHAR */


/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)
//static const size_t threshold = 128;
static const size_t NUM_LISTS = 16;

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;


typedef struct block
{
    /* Header contains size + allocation flag  */
    word_t header;
    
    /* Pointers were causing alignment issues so putting them in a union with
     * payload will allow them to never co-exist since payload will always be 
     * greater then or equal to 4*wsize 
     */

    /* This contains payload/pointers to next/prev block if a free block */
    union
    {
        /*
        * We don't know how big the payload will be.  Declaring it as an
        * array of size 0 allows computing its starting address using
        * pointer notation.
        */
        char payload[0];
        /* next and prev pointers for free block */
        struct 
        {
            struct block* next;
            struct block* prev;
        };
    };
    
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
/* pointer to first free block */
static  block_t* free_list_start[NUM_LISTS];

bool mm_checkheap(int lineno);
bool check_free_list();
bool check_bounds();

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void add_to_front(block_t* block, size_t place_index);
static void change_connections(block_t* block, size_t change_index);
static block_t *find_seg_fit(size_t asize);
static size_t find_best_index(size_t asize);
static size_t size_from_index(size_t index);


/*
 * Initializes Prologue header, Prologue footer and epilogue footer, assigns
 * the start of the heap, extends heap to chunksize and then initializes free
 * list pointers.
 */
bool mm_init(void) 
{

    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }

    /* Initialize Free Lists */
    for(size_t list_index = 0; list_index < NUM_LISTS; list_index++)
    {
        free_list_start[list_index] = NULL;
    }

    return true;
}

/*
 * Handles malloc request checking for block of required size in the respective
 * free list. Returns NULL if request wasn't completed.
 */
void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the respective free list for a fit
    block = find_seg_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
} 

/*
 * Takes pointer to a payload and then free's 
 * an allocted block from memory, and passes it to coalesce to see if 
 * merging with another free block is possible.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp); 
    size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);
}

/*
 * Takes pointer to a payload and size of reallocation and then
 * reallocates a given block to a bigger size, then copys the payload over.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    // Multiplication overflowed
    return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * Takes in size and then increases heap size accordingly rounding it to dsize
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

   
    // Initialize free block header/footer 
    block_t *block =  payload_to_header(bp);
  
    write_header(block, size, false);
   
    write_footer(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Takes in a pointer to a free block and free list index for 
 * that block then Adds the free block to the place before free_list_start. 
 * The free_list_start keeps moving to the end of the list and 
 * then back again so the list remains circular.
 */
static void add_to_front(block_t* block, size_t place_index)
{
    /* If list is empty then make block the start of it */
        if(free_list_start[place_index] == NULL)
        {
            free_list_start[place_index] = block;
            free_list_start[place_index] -> next = block;
            free_list_start[place_index] -> prev = block;
        }
        /* otherwise add it to before the free_list_start */
        else
        {
            block -> next = free_list_start[place_index];
            block -> prev = free_list_start[place_index] -> prev; 
            free_list_start[place_index] -> prev -> next  = block;
            free_list_start[place_index] -> prev = block;
        }
        return;
}

/* Takes in a pointer to free block and list index of that block then 
 * removes it from the repective free list 
 */
static void change_connections(block_t* block, size_t change_index)
{
    /* If there is only one block in the free list then make list empty */
    if(block -> prev == block && block-> next == block)
    {
        free_list_start[change_index] = NULL;
    }
    else
    {
        /* If block is the start of the list 
         * then move the start to next block
         */
        if(block == free_list_start[change_index])
        {
            free_list_start[change_index] = block -> next;
        }
        /* remove the block */
        block -> next -> prev = block -> prev;
        block -> prev -> next = block -> next;
    }
    
    return;
}


/*
 * Takes in pointer to a free block and then tries 
 * to merge it with adjacent free blocks if possible. 
 * If a merge is possible it first removes the free block from its free_list
 */
static block_t *coalesce(block_t * block) 
{
    block_t *block_next = find_next(block);
    block_t *block_prev = find_prev(block);

    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    size_t merge_index;
    merge_index = find_best_index(size);

    if (prev_alloc && next_alloc)              // Case 1
    {
        add_to_front(block, merge_index);
        
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        /* restore connections before splice */
        size_t next_size = get_size(block_next);
        size_t next_index = find_best_index(next_size);
        change_connections(block_next, next_index);

        size += get_size(block_next);
        write_header(block, size, false);
        write_footer(block, size, false);

        /* add the new bigger block to the free list */
        size_t merge_index = find_best_index(size);
        add_to_front(block, merge_index);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        /* restore connections before splice */
        size_t prev_size = get_size(block_prev);
        size_t prev_index = find_best_index(prev_size);
        change_connections(block_prev, prev_index);

        /* write header and footer for new merged block */
        size += get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;

        /* add the new bigger block to the free list */
        size_t merge_index = find_best_index(size);
        add_to_front(block, merge_index);
    }

    else                                        // Case 4
    {
        /* restore connections before splice */
        size_t next_size = get_size(block_next);
        size_t next_index = find_best_index(next_size);
        change_connections(block_next, next_index);

        size_t prev_size = get_size(block_prev);
        size_t prev_index = find_best_index(prev_size);
        change_connections(block_prev, prev_index);
         
        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;

        /* add the new bigger block to the free list */
        size_t merge_index = find_best_index(size);
        add_to_front(block, merge_index);
    }
    return block;
}

/*
 * Takes in ponter to free block and its size then
 * markes the header and footer of the block as allocated, 
 * inserts size in header and attemps to recycle unused 
 * part of the free block
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    size_t list_index = find_best_index(csize);

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);
        change_connections(block, list_index);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        list_index = find_best_index(csize - asize);
        add_to_front(block_next, list_index);
    }
    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
        change_connections(block, list_index);
    }
}

/*
 * Takes in size of allocation then finds a suitable list 
 * for that size.  It then returns a pointer to a free block 
 * of a size grater then or equal to asize.
 */
static block_t *find_seg_fit(size_t asize)
{
    size_t min_start_index = find_best_index(asize);

    block_t *block;

    for(size_t list_index = min_start_index; 
        list_index < NUM_LISTS; list_index++)
    {
        block = free_list_start[list_index];
        if(block == NULL)
        {
            continue;
        }
        if ((asize <= get_size(block)))
            {
                return block;
            }

        for (block = free_list_start[list_index] -> next; 
                (block != NULL && block != free_list_start[list_index]);
                     block = block -> next)
        {
            if ((asize <= get_size(block)))
            {
                return block;
            }
        }

    }
    return NULL; // no fit found
}

/* Checks the following:
* - All next/previous pointers are consistent,
* - All free list pointers are between mem_heap_lo() and mem_heap_hi()
* - All blocks in each list bucket fall within bucket size range 
*/
bool check_free_list()
{
    block_t *check_list = NULL;

    for(size_t index = 0; index < NUM_LISTS; index++)
    {
        if(free_list_start[index] == NULL)
        {
            continue;
        }
        if(*(&(free_list_start[index] -> header)) 
            > (unsigned long)mem_heap_hi())
        {
            return false;
        }
        if(free_list_start[index] -> next -> prev != free_list_start[index]) 
        {
            return false;
        } 
        if(free_list_start[index] -> prev -> next != free_list_start[index])
        {
            return false;
        }
        if((get_alloc(free_list_start[index])) != 0)
        {
            return false;
        }
        if (index != 15 && 
            (get_size(free_list_start[index])
                > size_from_index(index)))
        {

            return false;
        }

        for(check_list = free_list_start[index] -> next; 
            check_list != NULL && check_list != free_list_start[index]; 
            check_list = check_list -> next)
        {
            if(check_list -> prev -> next != check_list)
            {
                return false;
            }
            if(check_list -> next -> prev != check_list)
            {
                return false;
            }
            if((check_list -> header & alloc_mask) != 0)
            {
                return false;
            }
            if (index != 15 && 
                get_size(check_list)
                     > size_from_index(index))
            {
                return false;
            }
        }
    }
    return true;
}

/* Counts free blocks by iterating through every block and traversing free list 
 * by pointers and see if they match.
 * Also checks the following:
 * - coalescing: no two consecutive free blocks in the heap.
 * - Check each block’s header and footer:
 * - Check each block’s address alignment.
 * - Checks heap bounderies
 * - All next/previous pointers are consistent,
 * - All free list pointers are between mem_heap_lo() and mem_heap_hi()
 * - All blocks in each list bucket fall within bucket size range
 */
bool check_heap()
{
    /* Count free blocks on heap */
    int num_free_heap = 0;
    for(block_t *block = heap_start; block -> header != 1 ; 
            block = find_next(block))
    {
        if(get_size(block) > 0 && (!get_alloc(block)))
        {
            num_free_heap++;
        }

        if((!get_alloc(block))) 
        {
            if(get_alloc(find_next(block)) || (get_alloc(find_prev(block))))
            {
                assert(true);
            }
            else
            {
                return false;
            }
        }
    }
    
    /* Count free blocks on free lists */
    block_t *check_list = NULL;
    int num_free_list = 0;

    for(size_t index = 0; index < NUM_LISTS; index++)
    {
        if(free_list_start[index] == NULL)
        {
            continue;
        }
        else
        {
            num_free_list++;
        }
        for(check_list = free_list_start[index] -> next; 
            check_list != NULL && check_list != free_list_start[index]; 
            check_list = check_list -> next)
        {
            num_free_list++;
        }
    }

    /* Adjustment for some small uncoalased blocks by design */
    return(num_free_list - num_free_heap <= 1);
}

/* Checks epilogue and prologue blocks */
bool check_bounds()
{
    return (*(word_t*)((&(heap_start -> header)) - 1) == 1);
}

/* Heap checker does that following:
 * - Checks epilogue and prologue blocks
 * - Counts free blocks by iterating through every block and traversing 
 * free list by pointers and see if they match.
 * - coalescing: no two consecutive free blocks in the heap.
 * - Check each block’s header and footer:
 * - Check each block’s address alignment.
 * - Checks heap bounderies

 * It uses three helper functions. Their documentation is provided where they 
 * are written.
 */
bool mm_checkheap(int line)  
{ 
    if(!check_free_list())
    {
        printf("HEAP CHECK FAILED ON FREE LISTS. ");
        printf("Caller @line %d\n", line);
        return false;
    }
    if(!check_bounds())
    {
        printf("HEAP CHECK FAILED ON BOUND TESTS. ");
        printf("Caller @line %d\n", line);
        return false;
    }
    if(!check_heap())
    {
        printf("HEAP CHECK FAILED ON HEAP TEST. ");
        printf("Caller @line %d\n", line);
        return false;
    }
    return true;
}

/* Takes in index of a list and returns appropriate size class */
static size_t size_from_index(size_t index)
{
    size_t size = 0;

    if(index == 0)
    {
        size = 32;
    }
    else if(index == 1)
    {
        size = 64;
    }
    else if(index == 2)
    {
        size = 161;
    }
    else if(index == 3)
    {
        size = 200;
    }
    else if(index == 4)
    {
        size = 290;
    }
    else if(index == 5)
    {
        size = 350;
    }
    else if(index == 6)
    {
        size = 550;
    }
    else if(index == 7)
    {
        size = 760;
    }
    else if(index == 8)
    {
        size = 1100;
    }
    else if(index == 9)
    {
        size = 4140;
    }
    else if(index == 10)
    {
        size = 8240;
    }
    else if(index == 11)
    {
        size = 16433;
    }
    else if(index == 12)
    {
        size = 34033;
    }
    else if(index == 13)
    {
        size = 31033;
    }
    else if(index == 14)
    {
        size = 62033;
    }
    else
    {
        size = 0;
    }
    return size;
}

/* Takes in size of a block and returns appropriate free list index */
static size_t find_best_index(size_t asize)
{
    size_t index = 0;
    if(asize == 32)
    {
        index = 0;
    }
    else if(asize <= 64)
    {
        index = 1;
    }
    else if(asize <= 161)
    {
        index = 2;
    }
    else if(asize <= 200)
    {
        index = 3;
    }
    else if(asize <= 290)
    {
        index = 4;
    }
    else if(asize <= 350)
    {
        index = 5;
    }
    else if(asize <= 550)
    {
        index = 6;
    }
    else if(asize <= 760)
    {
        index = 7;
    }
    else if(asize <= 1100)
    {
        index = 8;
    }
    else if(asize <= 4140)
    {
        index = 9;
    }
    else if(asize <= 8240)
    {
        index = 10;
    }
    else if(asize <= 16433)
    {
        index = 11;
    }
    else if(asize <= 24033)
    {
        index = 12;
    }
    else if(asize <= 31033)
    {
        index = 13;
    }
    else if(asize <= 62033)
    {
        index = 14;
    }
    else
    {
        index = 15;
    }
    return index;
}


/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ad be ef 0a 0a 0a               *
 *                                                                           *
 *****************************************************************************
 */


/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
  
    word_t w = alloc ? (size | alloc_mask) : size;
   
    return w;

}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    assert(block != NULL);
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    
    block->header = pack(size, alloc);
  
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

// static word_t *find_prev_header(block_t *block)
// {
//     // Compute previous footer position as one word before the header
//     while(true)
//     {
//         if(extract_alloc( (&(block->header)) - i ))
//         {
//             return (&(block->header)) - i;
//         }
//     }

// }

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
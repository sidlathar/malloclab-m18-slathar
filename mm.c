/* SIDDHANTH LATHAR SLATHAR */
/*
 ******************************************************************************
 *                               mm-baseline.c                                *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

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
static bool IS_INIT = false;


typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    
    /* Pointers were causing alignment issues so putting them in a union with
     * payload will allow them to never co-exist since payload will always be greater then 
     or equal to 4*wsize */
    
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

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, word_t header);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);
static void write_next_header(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void add_to_front(block_t* block, size_t place_index);
static void change_connections(block_t* block, size_t change_index);
// static block_t *find_free_fit(size_t asize);
// static block_t *find_best_fit(size_t asize);
static block_t *find_seg_fit(size_t asize);
static size_t find_best_index(size_t asize);

/*
 * <what does mm_init do?>
 */
bool mm_init(void) 
{

    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true, 0); // Prologue footer
    start[1] = pack(0, true, 0); // Epilogue header

    start[1] = start[1] | 0x2;

    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    IS_INIT = true;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    IS_INIT = false;

    /* Initialize Free Lists */
    for(size_t list_index = 0; list_index < NUM_LISTS; list_index++)
    {
        free_list_start[list_index] = NULL;
    }

    return true;
}

/*
 * <what does mmalloc do?>
 */
void *malloc(size_t size) 
{
    printf("mallox \n");
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
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
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
 * <what does free do?>
 */
void free(void *bp)
{
    //printf("free\n");
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp); 
    size_t size = get_size(block);

    write_header(block, size, false);
    //write_next_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);
}

/*
 * <what does realloc do?>
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
 * <what does extend_heap do?>
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
    // if(IS_INIT)
    // {
    //     block -> header = block -> header | 0x2;
    // }
    // else
    // {
    //     block -> header = block -> header & (~0x2);
    // }
    write_footer(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    block -> header = block -> header | 0x2;

    // Coalesce in case the previous block was free
    return coalesce(block);
}

static void add_to_front(block_t* block, size_t place_index)
{
    //block_t* list = free_list_start[place_index];
    /* change next and prev pointers for new free_list_root */
        if(get_size(block) == 0 || get_alloc(block) == 1)
        {
            //printf("INVALID\n");
            return;
        }
        assert(block != NULL);
        //printf("INVALID33\n");
        assert(mm_checkheap(__LINE__));
        //printf("INVALID44\n");
        if(free_list_start[place_index] == NULL)
        {
            free_list_start[place_index] = block;
            free_list_start[place_index] -> next = block;
            free_list_start[place_index] -> prev = block;
        }
        else
        {
            block -> next = free_list_start[place_index];
            block -> prev = free_list_start[place_index] -> prev; 
            assert(block -> next != NULL);
            assert(block -> prev != NULL);
            free_list_start[place_index] -> prev -> next  = block;
            free_list_start[place_index] -> prev = block;
        }
        assert(mm_checkheap(__LINE__));
        return;
}


static void change_connections(block_t* block, size_t change_index)
{
    //block_t* list = free_list_start[change_index];
   //
    if(block -> prev == block && block-> next == block)
    {
        free_list_start[change_index] = NULL;
    }
    else
    {
        if(block == free_list_start[change_index])
        {
            free_list_start[change_index] = block -> next;
        }
        assert(block -> next != NULL);
        assert(block -> next  != NULL);
        //assert(block -> next -> header == 0); //not a alloc or free block
        assert(block -> prev  != NULL);
        block -> next -> prev = block -> prev;
        block -> prev -> next = block -> next;
    }
    return;
}

/*
 * <what does coalesce do?>
 */
static block_t *coalesce(block_t * block) 
{
    block_t *block_next = find_next(block);
    block_t *block_prev = NULL;
    bool next_alloc = get_alloc(block_next);
    bool prev_alloc = true;
    
    word_t head = block -> header;
    size_t size = get_size(block);

    /* check if prev alloc bit is set */
    if((head & 0x2) == 0x0) 
    {
        block_prev = find_prev(block);
        prev_alloc = false;
    }


    size_t merge_index;
    merge_index = find_best_index(size);

    if (prev_alloc && next_alloc)              // Case 1
    {
        write_header(block, size, false);
        write_footer(block, size, false);
        write_next_header(block, size, false);
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
        write_next_header(block, size, false);
        write_footer(block, size, false);

        /* change next and prev pointers for new free_list_root */
        size_t merge_index = find_best_index(size);
        add_to_front(block, merge_index);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        size_t prev_size = get_size(block_prev);
        size_t prev_index = find_best_index(prev_size);
        change_connections(block_prev, prev_index);

        /* write header and footer for new merged block */
        size += get_size(block_prev);
        write_header(block_prev, size, false);
        write_next_header(block, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;

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
        write_next_header(block, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;

        size_t merge_index = find_best_index(size);
        add_to_front(block, merge_index);
    }
    return block;
}

/*
 * <what does place do?>
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    size_t list_index = find_best_index(csize);

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        write_header(block, asize, true);
        write_next_header(block, asize, true);
        //REMOVE
        //write_footer(block, asize, true);
        //REMOVE
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
        write_next_header(block, csize, true);
        //REMOVE
        //write_footer(block, csize, true);
        //REMOVE
        change_connections(block, list_index);
    }
}

/*
 * <what does find_fit do?>
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;

    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {

        if (!(get_alloc(block)) && (asize <= get_size(block)))
        {
            return block;
        }
    }
    return NULL; // no fit found
}

// /*
//  * <what does find_fit do?>
//  */
// static block_t *find_best_fit(size_t asize)
// {
//     block_t *block;
//     block_t *best_fit = NULL;

//     size_t diff = 1;
//     size_t size;

//     for (block = free_list_start; (block != NULL); block = block -> next)
//     {
//         size = get_size(block);

//         if ((asize <= size))
//         {
//             if((size - asize <= diff) || diff == 1)
//             {
//                 best_fit = block;
//                 diff = size - asize;
//                 if(diff <= threshold)
//                 {
//                     return best_fit;
//                 }
//             }
//         }
//     }
//     return best_fit; // no fit found
// }


/*
 * <what does find_fit do?>
 */
static block_t *find_seg_fit(size_t asize)
{
    size_t min_start_index = find_best_index(asize);

    block_t *block;

    for(size_t list_index = min_start_index; list_index < NUM_LISTS; list_index++)
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

        for (block = free_list_start[list_index] -> next; (block != NULL && block != free_list_start[list_index]); block = block -> next)
        {
            if ((asize <= get_size(block)))
            {
                return block;
            }
        }

    }
    return NULL; // no fit found
}

/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)  
{ 
    /* you will need to write the heap checker yourself. As a filler:
     * one guacamole is equal to 6.02214086 x 10**23 guacas.
     * one might even call it
     * the avocado's number.
     *
     * Internal use only: If you mix guacamole on your bibimbap, 
     * do you eat it with a pair of chopsticks, or with a spoon? 
     * (Delete these lines!)
     */

    block_t *check_list = NULL;

    for(size_t index = 0; index < NUM_LISTS; index++)
    {
        if(free_list_start[index] == NULL)
        {
            continue;
        }
        assert(free_list_start[index] -> next -> prev == free_list_start[index]);
        assert(free_list_start[index] -> prev -> next == free_list_start[index]);
        //printf("%lu \n", (free_list_start[index] -> header & alloc_mask));
        //printf("index %zu \n", index);
        //printf("ss %zu \n", get_size(free_list_start[index]));
        //printf("head %lx \n", free_list_start[index] -> header);
        assert((get_alloc(free_list_start[index])) == 0);
        // assert((free_list_start[index] -> footer & alloc_mask) == 0);
        // assert(extract_size(free_list_start[index] -> footer) == extract_size(free_list_start[index] -> header));

        for(check_list = free_list_start[index] -> next; check_list != NULL && check_list != free_list_start[index]; check_list = check_list -> next)
        {
            assert(check_list -> prev -> next == check_list);
            assert(check_list -> next -> prev == check_list);
            assert((check_list -> header & alloc_mask) == 0);
            // assert((check_list -> footer & alloc_mask) == 0);
            // assert(extract_size(check_list -> footer) == extract_size(check_list -> header));
        }
    }
    return true;

}

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
static word_t pack(size_t size, bool alloc, word_t header)
{
    word_t w;
    if((header & 0x2) == 0x2)
    {
        w = alloc ? (size | alloc_mask) : size;
        w = w | 0x2;
    }
    else
    {
        w = alloc ? (size | alloc_mask) : size;
    }

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
    return asize - wsize;  //changed this
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
static void write_next_header(block_t *block, size_t size, bool alloc)
{
    block_t *block_next = find_next(block);
    if(alloc)
    {
        block_next->header = (block_next->header | 0x2);
    }
    else
    {
        block_next->header = (block_next->header & (~0x2));
    }  
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    
    block->header = pack(size, alloc, block->header);
  
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc, 0);
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
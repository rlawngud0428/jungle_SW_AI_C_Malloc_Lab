/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

#define WSIZE 4
#define DSIZE 8
// chunksize = 4096 byte (4kb) (page의 크기)
#define CHUNKSIZE (1 << 12)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define MIN(x, y) ((x) > (y) ? (y) : (x))

// 주소 + 할당여부
#define PACK(size, alloc) ((size) | (alloc))

// 포인터의 값 구하기
#define GET(p) (*(unsigned int *)(p))
// 포인터의 값 넣기
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 이번 블럭의 크기 구하기
#define GET_SIZE(p) (GET(p) & ~0x7)
// 이번 블럭의 할당 여부 구하기
#define GET_ALLOC(p) (GET(p) & 0x1)

// 현재 블럭의 header, footer 주소
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 이전, 다음 블럭 payload 주소
#define NEXT_BRKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)) - WSIZE))
#define PREV_BRKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)) - DSIZE))

// 이전, 다음 free 블럭 주소
#define PREV_FREE(bp) (*(char **)(bp))
#define NEXT_FREE(bp) (*(char **)((bp) + sizeof(void *)))

// heap의 시작 주소
static char * heap_list_p;

// free linked list의 시작 주소
static char * free_list_p;

// 미리 선언해야하는 함수들
static void *extended_heap(size_t words);
static void *coalesce(void *ptr);
static void *find_fit(size_t asize);
static void *place(char *bp, size_t asize);

static void *insert_freelist(char *bp);
static void *remove_freelist(char *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    free_list_p = NULL;
    // exception
    if ((heap_list_p = mem_sbrk(4*WSIZE)) == (void *)(-1)) {
        return -1;
    }

    // 기본적인 block 설정
    // padding
    PUT(heap_list_p, 0);
    // prologue header
    PUT(heap_list_p + (1*WSIZE), PACK(DSIZE, 1));
    // prologue footer
    PUT(heap_list_p + (2*WSIZE), PACK(DSIZE, 1));
    // epilogue header
    PUT(heap_list_p + (3*WSIZE), PACK(0, 1));

    heap_list_p += 2*WSIZE;

    if ((free_list_p = extended_heap(CHUNKSIZE/WSIZE)) == NULL) {
        return -1;
    }

    PREV_FREE(free_list_p) = NULL;
    NEXT_FREE(free_list_p) = NULL;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;
    size_t extendsize;
    char *bp;

    // 예외처리
    if (size == 0) {
        return NULL;
    }

    // 주어진 payload -> asize로 바꾸는 과정
    if (size < DSIZE) {
        asize = 2 * DSIZE + DSIZE;
    } else {
        asize = (DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE)) + DSIZE;
    }

    // find_fit에 성공하면, place로 split 할지 정하기 
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // find_fit 실패해서 extended_heap을 해야하는 경우 -> 늘려주고, place로 split 할지 정하기
    extendsize = MAX(asize, CHUNKSIZE) / WSIZE;
    if ((bp = extended_heap(extendsize)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

// 힙 영역 안에 더이상 할당할 수 없다면, 힙을 늘려야 함.
// 영역을 늘리고, epilogue에 대한 처리를 잘 해줄 것. + coalescing이 필요한걸로 앎.
// CHUCK_SIZE가 필요하려나.. (책 저자는 쓰긴 하던데.) -> 무조건 필요
static void *extended_heap(size_t words) {
    char * bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // epilogue header
    PUT(HDRP(NEXT_BRKP(bp)), PACK(0, 1));

    void *temp = coalesce(bp);
    insert_freelist(temp);
    return temp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    // coalescing 해야함
    void *free_ptr = coalesce(ptr);
    insert_freelist(free_ptr);
}

static void *coalesce(void *ptr) {
    int prev_alloc = GET_ALLOC(HDRP(PREV_BRKP(ptr)));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BRKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    // case 1. 앞 뒤 블럭 전부다 alloc 1
    if (prev_alloc && next_alloc) {
        return ptr;
    }
    // case 2. 앞 블럭 alloc 0 뒤 블럭 alloc 1
    else if (!prev_alloc && next_alloc) {
        char * prev = PREV_BRKP(ptr);
        remove_freelist(prev);
        PUT(FTRP(ptr), PACK((size + GET_SIZE(HDRP(prev))), 0));
        PUT(HDRP(prev), PACK((size + GET_SIZE(HDRP(prev))), 0));
        ptr = prev;
    }
    // case 3. 앞 블럭 alloc 1 뒤 블럭 alloc 0
    else if (prev_alloc && !next_alloc) {
        char * next = NEXT_BRKP(ptr);
        remove_freelist(next);
        PUT(HDRP(ptr), PACK((size + GET_SIZE(HDRP(next))), 0));
        PUT(FTRP(next), PACK((size + GET_SIZE(HDRP(next))), 0));
    }
    // case 4. 앞 뒤 블럭 전부다 alloc 0
    else {
        char * prev = PREV_BRKP(ptr);
        char * next = NEXT_BRKP(ptr);
        remove_freelist(prev);
        remove_freelist(next);
        PUT(FTRP(next), PACK((size + GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next))), 0));
        PUT(HDRP(prev), PACK((size + GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next))), 0));
        ptr = prev;
    }
    return ptr;
}

// free된 블럭 중 할당할 수 있는 공간 찾기
static void *find_fit(size_t asize) {
    char * bp = free_list_p;

    while (1) {
        // epilogue 만나면 종료
        if (bp == 0) {
            break;
        }
        // free인 블록
        if (GET_ALLOC(HDRP(bp)) == 0) {
            // 의 크기가 지금 할당하려는 asize보다 크다면
            if (GET_SIZE(HDRP(bp)) >= asize) {
                return bp;
            } else {
                bp = NEXT_FREE(bp);
            }
        } else {
            bp = NEXT_FREE(bp);
        }
    }
    return NULL;
}

// free된 블럭에 malloc을 하고 남은 공간에 대한 split, 남은 공간이 작으면 그냥 padding으로 처리
static void *place(char *bp, size_t asize) {
    size_t size = GET_SIZE(HDRP(bp));

    if (size - asize >= 24) {
        remove_freelist(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BRKP(bp)), PACK(size-asize, 0));
        PUT(FTRP(NEXT_BRKP(bp)), PACK(size-asize, 0));
        insert_freelist(NEXT_BRKP(bp));
    } else {
        remove_freelist(bp);
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }

    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;

    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //     return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize)
    //     copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;

    // 일단 지금 있는 거에서 늘려봐야한다.
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    char *next = NEXT_BRKP(ptr);
    char *bp;
    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t asize;

    if (size < DSIZE) {
        asize = (2 * DSIZE) + DSIZE;
    } else {
        asize = (DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE)) + DSIZE;
    }

    if (GET_ALLOC(HDRP(next)) == 0 && (old_size + GET_SIZE(HDRP(next))) >= asize) {
        if (old_size + GET_SIZE(HDRP(next)) - asize >= 24) {
            remove_freelist(next);
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            PUT(HDRP(NEXT_BRKP(ptr)), PACK(old_size + GET_SIZE(HDRP(next)) - asize, 0));
            PUT(FTRP(NEXT_BRKP(ptr)), PACK(old_size + GET_SIZE(HDRP(next)) - asize, 0));
            insert_freelist(NEXT_BRKP(ptr));
        } else {
            remove_freelist(next);
            PUT(HDRP(ptr), PACK(old_size + GET_SIZE(HDRP(next)), 1));
            PUT(FTRP(ptr), PACK(old_size + GET_SIZE(HDRP(next)), 1));
        }
            
            return ptr;
    } else {
        if ((bp = find_fit(asize)) != NULL) {
            place(bp, asize);
            memcpy(bp, ptr, MIN(old_size-(2 * WSIZE), size));
            mm_free(ptr);
            return bp;
        } else {
            extended_heap(asize / WSIZE);
            bp = find_fit(asize);
            place(bp, asize);
            memcpy(bp, ptr, MIN(old_size-(2 * WSIZE), size));
            mm_free(ptr);
            return bp;
        }
    }
}

static void *insert_freelist(char *bp) {
    void * temp = free_list_p;
    if (temp == NULL) {
        NEXT_FREE(bp) = NULL;
        PREV_FREE(bp) = NULL;
        free_list_p = bp;
    } else {
        NEXT_FREE(bp) = temp;
        PREV_FREE(bp) = NULL;
        PREV_FREE(temp) = bp;
        free_list_p = bp;
    }
}

static void *remove_freelist(char *bp) {
    void *prev = PREV_FREE(bp);
    void *next = NEXT_FREE(bp);

    if (!prev && !next) {
        free_list_p = NULL;
    } else if (prev && !next) {
        NEXT_FREE(prev) = NULL;
    } else if (!prev && next) {
        PREV_FREE(next) = NULL;
        free_list_p = next;
    } else {
        NEXT_FREE(prev) = next;
        PREV_FREE(next) = prev;
    }
}

// explicit 구현 과정
// block 구조 확장
// free list의 시작점 관리
// find_fit 변경
// place 변경 (할당 시 처리)
// free 변경
// coalescing 변경
// free list insert
// free list remove
// mm_realloc 고려
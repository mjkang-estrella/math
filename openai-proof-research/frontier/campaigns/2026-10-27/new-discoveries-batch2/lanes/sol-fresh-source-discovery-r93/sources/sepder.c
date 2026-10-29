#include "sepder_internal.h"

#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>

#include <flint/fmpz_vec.h>

typedef struct
{
    slong max_n;
    fmpz **row;
} diagonal_table_t;

typedef struct
{
    slong max_n;
    fmpz *s_plus;
    fmpz *s_minus;
    diagonal_table_t d;
    diagonal_table_t d_plus;
    diagonal_table_t d_minus;
} workspace_t;

static int
diagonal_valid(slong n, slong k)
{
    return n >= 1 && -(n - 1) <= k && k <= n - 1;
}

static slong
diagonal_width(const diagonal_table_t *table, slong n)
{
    return FLINT_MIN(n, table->max_n - n + 1);
}

/* Inversion is a bijection within each of T, T^plus, and T^minus, and it
   sends diagonal k to diagonal -k. Rows therefore store only k >= 0. For a
   computation ending at N, causality further restricts row n to k <= N - n. */
static fmpz *
diagonal_entry(diagonal_table_t *table, slong n, slong k)
{
    assert(FLINT_ABS(k) < diagonal_width(table, n));
    return table->row[n] + FLINT_ABS(k);
}

static const fmpz *
diagonal_entry_const(const diagonal_table_t *table, slong n, slong k)
{
    assert(FLINT_ABS(k) < diagonal_width(table, n));
    return table->row[n] + FLINT_ABS(k);
}

static void
diagonal_table_init(diagonal_table_t *table, slong max_n)
{
    slong n;

    table->max_n = max_n;
    table->row = flint_calloc((size_t) max_n + 1, sizeof(fmpz *));
    for (n = 1; n <= max_n; ++n)
        table->row[n] = _fmpz_vec_init(diagonal_width(table, n));
}

static void
diagonal_table_clear(diagonal_table_t *table)
{
    slong n;

    if (table->row == NULL)
        return;

    for (n = 1; n <= table->max_n; ++n)
        _fmpz_vec_clear(table->row[n], diagonal_width(table, n));
    flint_free(table->row);
    table->row = NULL;
    table->max_n = 0;
}

static void
workspace_init(workspace_t *workspace, slong max_n)
{
    workspace->max_n = max_n;
    workspace->s_plus = _fmpz_vec_init(max_n + 1);
    workspace->s_minus = _fmpz_vec_init(max_n + 1);
    diagonal_table_init(&workspace->d, max_n);
    diagonal_table_init(&workspace->d_plus, max_n);
    diagonal_table_init(&workspace->d_minus, max_n);
}

static void
workspace_clear(workspace_t *workspace)
{
    if (workspace->s_plus != NULL)
        _fmpz_vec_clear(workspace->s_plus, workspace->max_n + 1);
    if (workspace->s_minus != NULL)
        _fmpz_vec_clear(workspace->s_minus, workspace->max_n + 1);
    diagonal_table_clear(&workspace->d);
    diagonal_table_clear(&workspace->d_plus);
    diagonal_table_clear(&workspace->d_minus);
    workspace->s_plus = NULL;
    workspace->s_minus = NULL;
    workspace->max_n = 0;
}

void
sd_result_init(sd_result_t *result)
{
    if (result == NULL)
        return;
    result->max_n = -1;
    result->s = NULL;
    result->a0 = NULL;
    result->b = NULL;
}

void
sd_result_clear(sd_result_t *result)
{
    slong length;

    if (result == NULL)
        return;

    length = result->max_n >= 0 ? result->max_n + 1 : 0;
    if (result->s != NULL)
        _fmpz_vec_clear(result->s, length);
    if (result->a0 != NULL)
        _fmpz_vec_clear(result->a0, length);
    if (result->b != NULL)
        _fmpz_vec_clear(result->b, length);
    sd_result_init(result);
}

static int
size_is_valid(slong max_n)
{
    size_t count;

    if (max_n < 0 || max_n > (WORD_MAX - 1) / 2)
        return 0;

    count = (size_t) max_n + 1;
    if (count > SIZE_MAX / sizeof(fmpz *))
        return 0;
    if (count > SIZE_MAX / sizeof(fmpz))
        return 0;
    return 1;
}

static void
compute_ordinary_row(workspace_t *workspace, sd_result_t *result, slong n)
{
    slong i;

    for (i = 1; i < n; ++i)
    {
        slong j = n - i;
        if (i == 1)
        {
            fmpz_add(workspace->s_plus + n,
                     workspace->s_plus + n,
                     result->s + j);
            fmpz_add(workspace->s_minus + n,
                     workspace->s_minus + n,
                     result->s + j);
        }
        else
        {
            fmpz_addmul(workspace->s_plus + n,
                        workspace->s_minus + i,
                        result->s + j);
            fmpz_addmul(workspace->s_minus + n,
                        workspace->s_plus + i,
                        result->s + j);
        }
    }

    fmpz_add(result->s + n,
             workspace->s_plus + n,
             workspace->s_minus + n);
}

/* A direct sum avoids diagonal k exactly when both components avoid their
   local diagonal k. Diagonals outside a component's range are vacuously
   empty, so its empty count there is its full class count. */
static void
compute_sum_empty_diagonal(const workspace_t *workspace,
                           const sd_result_t *result,
                           slong n,
                           slong k,
                           fmpz *value)
{
    slong i;

    for (i = 1; i < n; ++i)
    {
        slong j = n - i;
        const fmpz *right = diagonal_valid(j, k)
            ? diagonal_entry_const(&workspace->d, j, k)
            : result->s + j;

        if (i == 1)
        {
            /* The singleton is empty on every local diagonal except zero. */
            if (k != 0)
                fmpz_add(value, value, right);
        }
        else
        {
            const fmpz *left = diagonal_valid(i, k)
                ? diagonal_entry_const(&workspace->d_minus, i, k)
                : workspace->s_minus + i;

            fmpz_addmul(value, left, right);
        }
    }
}

/* In a skew sum with component sizes i and j, separation = i - j is the
   empty diagonal between their possible ranges. Below it only the left
   component can meet the diagonal; above it only the right component can. */
static void
compute_skew_empty_diagonal(const workspace_t *workspace,
                            const sd_result_t *result,
                            slong n,
                            slong k,
                            fmpz *value)
{
    slong i;

    for (i = 1; i < n; ++i)
    {
        slong j = n - i;
        slong separation = i - j;

        if (k < separation)
        {
            slong left_k = k + j;

            if (i == 1)
            {
                if (left_k != 0)
                    fmpz_add(value, value, result->s + j);
            }
            else if (diagonal_valid(i, left_k))
            {
                fmpz_addmul(value,
                            diagonal_entry_const(&workspace->d_plus,
                                                 i,
                                                 left_k),
                            result->s + j);
            }
            else
            {
                fmpz_addmul(value,
                            workspace->s_plus + i,
                            result->s + j);
            }
        }
        else if (k == separation)
        {
            if (i == 1)
                fmpz_add(value, value, result->s + j);
            else
                fmpz_addmul(value,
                            workspace->s_plus + i,
                            result->s + j);
        }
        else
        {
            slong right_k = k - i;
            const fmpz *right = diagonal_valid(j, right_k)
                ? diagonal_entry_const(&workspace->d, j, right_k)
                : result->s + j;

            if (i == 1)
                fmpz_add(value, value, right);
            else
                fmpz_addmul(value,
                            workspace->s_plus + i,
                            right);
        }
    }
}

static void
compute_diagonal_row(workspace_t *workspace,
                     const sd_result_t *result,
                     slong n)
{
    slong width = diagonal_width(&workspace->d, n);
    slong k;

    #pragma omp parallel for schedule(dynamic, 4) if(n >= 32)
    for (k = 0; k < width; ++k)
    {
        fmpz *sum_value = diagonal_entry(&workspace->d_plus, n, k);
        fmpz *skew_value = diagonal_entry(&workspace->d_minus, n, k);
        fmpz *total_value = diagonal_entry(&workspace->d, n, k);

        compute_sum_empty_diagonal(workspace, result, n, k, sum_value);
        compute_skew_empty_diagonal(workspace, result, n, k, skew_value);
        fmpz_add(total_value, sum_value, skew_value);
    }
}

static int
notify_observer(const workspace_t *workspace,
                const sd_result_t *result,
                slong n,
                sd_row_observer_fn observer,
                void *observer_context)
{
    sd_row_view_t row;

    if (observer == NULL)
        return 1;

    row.n = n;
    row.diagonal_count = diagonal_width(&workspace->d, n);
    row.s = result->s + n;
    row.s_plus = workspace->s_plus + n;
    row.s_minus = workspace->s_minus + n;
    row.d = workspace->d.row[n];
    row.d_plus = workspace->d_plus.row[n];
    row.d_minus = workspace->d_minus.row[n];
    return observer(&row, observer_context);
}

int
sd_compute_internal(sd_result_t *result,
                    slong max_n,
                    sd_progress_fn progress,
                    void *progress_context,
                    sd_row_observer_fn observer,
                    void *observer_context)
{
    workspace_t workspace = {0};
    slong n;
    int status = SD_SUCCESS;

    if (result == NULL)
        return SD_ERROR_INVALID_ARGUMENT;
    if (!size_is_valid(max_n))
        return max_n < 0 ? SD_ERROR_INVALID_ARGUMENT : SD_ERROR_SIZE_OVERFLOW;

    sd_result_clear(result);
    result->max_n = max_n;
    result->s = _fmpz_vec_init(max_n + 1);
    result->a0 = _fmpz_vec_init(max_n + 1);
    result->b = _fmpz_vec_init(max_n + 1);

    fmpz_one(result->s);
    fmpz_one(result->b);
    if (max_n == 0)
        return SD_SUCCESS;

    workspace_init(&workspace, max_n);

    fmpz_one(result->s + 1);
    fmpz_one(result->a0 + 1);

    if (!notify_observer(&workspace,
                         result,
                         1,
                         observer,
                         observer_context))
    {
        status = SD_ERROR_OBSERVER;
        goto cleanup;
    }
    if (progress != NULL)
        progress(1, max_n, progress_context);

    for (n = 2; n <= max_n; ++n)
    {
        compute_ordinary_row(&workspace, result, n);
        compute_diagonal_row(&workspace, result, n);
        fmpz_set(result->b + n, diagonal_entry(&workspace.d, n, 0));
        fmpz_sub(result->a0 + n, result->s + n, result->b + n);

        if (!notify_observer(&workspace,
                             result,
                             n,
                             observer,
                             observer_context))
        {
            status = SD_ERROR_OBSERVER;
            goto cleanup;
        }
        if (progress != NULL)
            progress(n, max_n, progress_context);
    }

cleanup:
    workspace_clear(&workspace);
    return status;
}

int
sd_compute(sd_result_t *result,
           slong max_n,
           sd_progress_fn progress,
           void *progress_context)
{
    return sd_compute_internal(result,
                               max_n,
                               progress,
                               progress_context,
                               NULL,
                               NULL);
}

const char *
sd_error_string(int error_code)
{
    switch (error_code)
    {
        case SD_SUCCESS:
            return "success";
        case SD_ERROR_INVALID_ARGUMENT:
            return "invalid argument";
        case SD_ERROR_SIZE_OVERFLOW:
            return "requested size overflows an internal index";
        default:
            return "unknown error";
    }
}

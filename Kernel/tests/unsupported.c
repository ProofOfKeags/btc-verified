/* Compiles against the full upstream header but must fail to link against this
 * partial implementation: no stub silently pretends the accessor is supported. */
#include <bitcoinkernel.h>

int main(void)
{
    const unsigned char bytes[] = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    btck_Transaction* tx = btck_transaction_create(bytes, sizeof(bytes));
    if (tx == NULL) return 1;
    const uint32_t locktime = btck_transaction_get_locktime(tx);
    btck_transaction_destroy(tx);
    return (int)locktime;
}

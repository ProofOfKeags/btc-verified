/* This client must compile against the canonical header but fail to link.
 * Context APIs are deliberately outside the implemented transaction slice.
 */
#include <kernel/bitcoinkernel.h>

int main(void)
{
    btck_Context* context = btck_context_create((btck_ContextOptions*)0);
    btck_context_destroy(context);
    return context != 0;
}

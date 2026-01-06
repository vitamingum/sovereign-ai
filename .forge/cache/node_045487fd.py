def test(ctx, result):
    import os
    return os.path.exists('messages') and os.access('messages', os.R_OK)
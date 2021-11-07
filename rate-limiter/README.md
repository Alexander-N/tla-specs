# Rate limiter

Race condition described in the [redis documentation](https://redis.io/commands/incr/#pattern-rate-limiter-2). If the setting of the expiry time of a request counter is aborted by some reason, say a crash or network problem, then the counter will not be reset causing this IP address to be blocked forever.

From https://redis.io/commands/incr/#pattern-rate-limiter-2:
> ## Pattern: Rate limiter 2
> An alternative implementation uses a single counter, but is a bit more complex to get it right without race conditions. We'll examine different variants.
>
> ```
> FUNCTION LIMIT_API_CALL(ip):
> current = GET(ip)
> IF current != NULL AND current > 10 THEN
>     ERROR "too many requests per second"
> ELSE
>     value = INCR(ip)
>     IF value == 1 THEN
>         EXPIRE(ip,1)
>     END
>     PERFORM_API_CALL()
> END
> ```
> The counter is created in a way that it only will survive one second, starting from the first request performed in the current second. If there are more than 10 requests in the same second the counter will reach a value greater than 10, otherwise it will expire and start again from 0.
>
> **In the above code there is a race condition.** If for some reason the client performs the INCR command but does not perform the EXPIRE the key will be leaked until we'll see the same IP address again.
>
> This can be fixed easily turning the INCR with optional EXPIRE into a Lua script that is send using the EVAL command (only available since Redis version 2.6).
>
> ```
> local current
> current = redis.call("incr",KEYS[1])
> if current == 1 then
>     redis.call("expire",KEYS[1],1)
> end
> ```

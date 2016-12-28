## Recoverability

In `NServiceBus` a message can be either sucessfully processed or moved to an error queue. The latter happens when processing fails `MaxAttempt` times.

### `TransportTransactionMode.TransactionScope`

The [NServiceBus]() recoverability sub-system has been modeled with following assumptions:
  
 * All side-effects can be modelled as queue operations. In particular business logic and persister side effects are modelled as single message sent to `Effects` queue.  
 * Queues participate in distributed transaction. 
 * RetryCounter is non-transactional and has a life-time of the `Receiver`.  


```

                                     +-------------+
                                     |  Errors     |
                                     +------^------+
    +-------+     +------------+            |
    | Input +---> |  Receiver  +------------+
    +-------+     +------------+            |
                                     +------v------+
                                     |  Effects    |
                                     +-------------+
 ```

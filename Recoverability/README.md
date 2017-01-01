## Recoverability

In `NServiceBus` a message can be either sucessfully processed or moved to an error queue. The latter happens when processing fails `MaxAttempt` times.

### `TransportTransactionMode.TransactionScope`

Model specified in [Recoverability.tla]() is a simplification of a digital system, in this case [NServiceBus]() recoverability subsystem. It omits some aspects of the system and preserves others, based on their importance from verification perspective. 

The model has been crated to:
 * Validate that `Error` and `Effects` are exclusive. `EitherFailedOrProcessed` invariant.
 * Validate what are conditions under which no more than `MaxAttempt` will get performed. `NoMoreThanMaxAttempts` invariant.

What has been omited:

 * Immediate and delayed retries - we do not care what is the time between processing attempts
 * Custom failure headers - we are not interested in failure message transformations
 * Message serialization errors - poison message handling is treated as a separate mechanism
 * Modular design - logic residing in [Core]() and [Transport]() module are modeled as a single PlusCalc process
 * Details of user code logic - all business logic side effects are modeled as a message being sent to `Effects` queue
 * Endpoint concurrency limit - we put no cap on the concurrency level 
 * [Temporary] Competing consumers deployments - there is a single `Receiver` running at any given point in time
 * [Temporary] Every input message participate in at most one transaction at any given point in time
What has been preserved:
  
 * Queues' data is stored in stable storage and operations participate in atomic distributed transactions.
 * Transactions can time out
 * Number of processing attempts is stored by `Receiver`'s in memory
 * `Receiver` can crash and later recover losing attempts cache
 * Message handling in `Receiver` can either fail or succeed

Granularity of the model is at the level of transaction, queue and counter operations - meaning that a single operation one of the three translates roughly to a single step in the specification. 

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

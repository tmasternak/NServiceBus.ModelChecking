## Recoverability

In `NServiceBus` a message can be either sucessfully processed or moved to an error queue. The latter happens when processing fails `MaxAttempt` times.

```

                         +------------+
                        |  Errors    |
                        +------+-----+
                               ^
                               |
                  +------------+--+---------+
                  |               | Attempts|
+----------+      |               | Cache   |
|  Input   +----> |               +---------+
+----------+      |   Receiver              |
                  |                         |
                  |                         |
                  +------------+------------+
                               |
                               |
                        +------v-----+
                        |  Effects   |
                        +------------+

 ```

### Model

Model specified in [Recoverability.tla]() is a simplification of a digital system, in this case [NServiceBus]() recoverability subsystem. It omits some aspects of the system and preserves others, based on their importance from verification perspective. 

The model has been crated to:
 * Validate that `Error` and `Effects` are exclusive. [`EitherFailedOrProcessed`](https://github.com/tmasternak/NServiceBus.ModelChecking/blob/master/Recoverability/Recoverability.tla#L140).
 * Validate what are conditions under which no more than `MaxAttempt` will get performed. [`NoMoreThanMaxAttempts`](https://github.com/tmasternak/NServiceBus.ModelChecking/blob/master/Recoverability/Recoverability.tla#L144).

What has been omited:

 * Immediate and delayed retries - we do not care what is the time between processing attempts
 * Custom failure headers - we are not interested in failure message transformations
 * Message serialization errors - poison message handling is treated as a separate mechanism
 * Modular design - logic residing in [Core]() and [Transport]() module are modeled as a single PlusCalc process
 * Details of user code logic - all business logic side effects are modeled as a message being sent to `Effects` queue
 * Endpoint concurrency limit - we put no cap on the concurrency level 
 * **Temporary** Every input message participate in at most one transaction at any given point in time

What has been preserved:
  
 * Queues' data is stored in stable storage and operations participate in atomic distributed transactions.
 * Transactions can time out
 * Number of processing attempts is stored by the `Receiver` in memory
 * `Receiver` can crash and later recover losing attempts cache
 * There can be more than one `Receiver` aka competing consumer
 * Message handling in `Receiver` can either fail or succeed
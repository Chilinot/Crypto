(*
    REPRESENTATION CONVENTION: 
        Represents an integer queue according to the FIFO-pattern.
        
        PARAMETERS:
            Queue(first, end, size):
                first - The integers at the head of the queue.
                end   - The integers at the back of the queue.
                size  - The current amount of elements in the entire queue.
    REPRESENTATION INVARIANT: 
        None.
*)
abstype queue = Queue of int list * int list * int with

    (*  
        mkQueue()
        TYPE:   unit -> queue
        PRE:    None
        POST:   An empty queue.
    *)
    (*  TIME COMPLEXITY: Theta(1) always. *)
    fun mkQueue () = Queue([], [], 0)

    (* 
        normalize q
        TYPE:   queue -> queue
        PRE:    True
        POST:   A normalized version of the queue.
    *)
    (*  TIME COMPLEXITY: Theta(n) *)
    fun normalize (Queue([], b, n)) = Queue(List.rev(b), [], n)
      | normalize (q)               = q
    
    (* 
        enqueue(q, e)
        TYPE:   queue * int -> queue
        PRE:    True
        POST:   The queue q, where the element e has been added to the end of it.
    *)
    (*  TIME COMPLEXITY: Theta(1) always. *)
    fun enqueue (Queue(f, b, n), e) = Queue(f, e::b, n + 1)
    
    (* 
        enqueueList(q, l)
        TYPE:   queue * int list -> queue
        PRE:    True
        POST:   The queue q, where each element in l has been added to the end.
    *)
    (*  VARIANT: Length of l. 
        TIME COMPLEXITY: Theta(n) always. *)
    fun enqueueList (q, [])                = q
      | enqueueList (Queue(f, b, n), h::l) = enqueueList(Queue(f, h::b, n+1), l)
      
    (* 
        merge(q1, q2)
        TYPE:   queue * queue -> queue
        PRE:    True
        POST:   The queue q1, where each element in q2 has been added to the end.
    *)
    (*  TIME COMPLEXITY: Theta(n) always. *)
    fun merge (q, Queue(t, f, _)) = enqueueList(enqueueList(q, t), List.rev(f))
    
    (* 
        dequeue q
        TYPE:   queue -> queue
        PRE:    q is nonempty
        POST:   Queue q, where the head of the queue has been removed.
        SIDE-EFFECTS: Raises Fail if the queue is empty.
    *)
    (*  TIME COMPLEXITY: O(n) *)
    fun dequeue (Queue([], [], n))       = raise Fail "Can not dequeue on empty queue!"
      | dequeue (q as (Queue([], _, _))) = dequeue(normalize(q))
      | dequeue (Queue(x::f, b, n))      = Queue(f, b, n-1)
      
    (* 
        dequeueButt q
        TYPE:   queue -> queue
        PRE:    q is nonempty
        POST:   Queue q, where the last element in the queue has been removed.
        SIDE-EFFECTS: Raises Fail if the queue is empty.
    *)
    (*  TIME COMPLEXITY: O(n) *)
    fun dequeueButt (Queue([], [], _))  = raise Fail "Can not dequeueButt on empty queue!"
      | dequeueButt (Queue(f, [], n))   = dequeueButt(Queue([], List.rev(f), n))
      | dequeueButt (Queue(f, x::b, n)) = Queue(f, b, n - 1)
    
    (* 
        head q
        TYPE: queue -> int
        PRE:    q is nonempty
        POST:   The first element in q.
        SIDE-EFFECTS: Raises Fail if q is empty.
    *)
    (*  TIME COMPLEXITY: O(n) *)
    fun head (Queue([], [], _))       = raise Fail "Can not retrieve head on empty queue!"
      | head (q as (Queue([], b, _))) = head(normalize(q))
      | head (Queue(x::f, b, _))      = x
      
    (* 
        butt q
        TYPE:   queue -> int
        PRE:    q is nonempty
        POST:   The last element in q.
        SIDE-EFFECTS: Raises Fail if q is empty.
    *)
    (*  TIME COMPLEXITY: O(n) *)
    fun butt (Queue([], [], _))  = raise Fail "Can not retrieve butt on empty qeueue!"
      | butt (Queue(f, [], n))   = butt(Queue([], List.rev(f), n))
      | butt (Queue(_, x::b, _)) = x
    
    (* 
        isEmpty q
        TYPE:   queue -> bool
        PRE:    True
        POST:   True if q is empty, else false.
    *)
    (*  TIME COMPLEXITY: Theta(1) always. *)
    fun isEmpty (Queue([], [], _)) = true
      | isEmpty (q)                = false
      
    (* 
        queueSize q
        TYPE:   queue -> int
        PRE:    True
        POST:   The amount of elements in q.
    *)
    (*  TIME COMPLEXITY: Theta(1) always. *)
    fun queueSize(Queue(_, _, n)) = n
    
    (* 
        extract(q, n, start)
        TYPE:   queue * int * int list -> queue * int list
        PRE:    n can not be of a greater value than the size of q.
        POST:   The modified version of q missing the first n elements, and the extracted elements appended to start.
                The first n amount of elements has been removed from q and appended to the list start.
        SIDE-EFFECTS: Raises Fail if q is empty, or if n is greater than the size of q.
    *)
    (*  VARIANT: Size of n.
        TIME COMPLEXITY: Theta(n) *)
    fun extract(q, 0, l) = (q, List.rev(l))
      | extract(q as (Queue([], [], nq)), n, l) = raise Fail("Extract out of bounds! nq:" ^ Int.toString(nq) ^ " n:" ^ Int.toString(n))
      | extract(q as (Queue([], _, _)), n, l)   = extract(normalize(q), n, l)
      | extract(Queue(x::f, b, nq), n, l)       = extract(Queue(f, b, nq - 1), n - 1, x::l)
      
    (* 
        nth(q, n)
        TYPE:   queue * int -> int
        PRE:    n can not be of a greater value than the size of q.
        POST:   The n'th element in the queue q.
        SIDE-EFFECTS: Raises Fail if q is empty, or if n is greater than the size of q.
    *)
    (*  VARIANT: Size of n. 
        TIME COMPLEXITY: Theta(n) *)
    fun nth (Queue([], [], nq), n) = raise Fail ("Nth out of bounds! nq:" ^ Int.toString(nq) ^ " n:" ^ Int.toString(n))
      | nth (q as (Queue([], b, _)), n) = nth(normalize(q), n)
      | nth (Queue(x::f, b, _), 0) = x
      | nth (Queue(x::f, b, nq), n) = nth(Queue(f, b, nq-1), n - 1)
end


(*
    REPRESENTATION CONVENTION: 
        Represents the jokers A and B for usage in the Solitaire cryptographic algorithm.
    REPRESENTATION INVARIANT: 
        None.
*)
datatype joker = A | B

(*
    REPRESENTATION CONVENTION:
        Represents the deck of cards for usage in the Solitaire cryptographic algorithm.
        In this case, each card is stored as its integer value in any of the three queues depending on where it is positioned in the deck relative to the two jokers.
        The jokers positions are stored relative to each other, either as (A,B) or (B,A). 
        Their exact position isn't directly stored, but the cards in relation to the two jokers are stored in three separate queues.
        
        Parameter explanation:
            Deck(top, middle, bottom, (joker1, joker2)):
                Top:    The values above the top joker.
                Middle: The values between the two jokers.
                Bottom: The values below the bottom joker.
                Joker1: The top joker.
                Joker2: The bottom joker.
            
    REPRESENTATION INVARIANT:
        The values stored in the deck can not be negative.
        
        Joker1 and Joker2 can not be of the same value. 
        They have to be either (A,B) or (B,A), not (B,B) or (A,A).
*)
datatype deck = Deck of queue * queue * queue * (joker * joker)

(*
   ===== HELPER FUNCTIONS =====
*)

(* 
    makeDeck l
    TYPE:    int list -> deck
    PRE:     l is the list of values to store in the deck.
    POST:    A new deck, with each element in l.
*)
(*  TIME COMPLEXITY: Theta(n) always. *)
fun makeDeck (l) = 
    let
        (* 
            makeDeck(d, l)
            TYPE:   deck * list -> deck
            PRE:    True
            POST:   Deck d with all elements in l appended to the first queue.
            EXAMPLE:
                Add the list of values [1,2,3,4] to the deck d:
                    makeDeck'(d, [1,2,3,4])
        *)
        (*  VARIANT: Length of l. *)
        fun makeDeck'(d, []) = d
          | makeDeck'(Deck(t, m, b, order), x::l) = makeDeck'(Deck(enqueue(t, x), m, b, order), l)
    in
        makeDeck'(Deck(mkQueue(), mkQueue(), mkQueue(), (A,B)), l)
    end

(*
    xList n
    TYPE:    int -> char list
    PRE:     n >= 0
    POST:    List with n amount of the character X.
    EXAMPLE: xList 3 = [#"X", #"X", #"X"]
*)
(*  VARIANT: Size of n. 
    TIME COMPLEXITY: Theta(n) always. *)
fun xList (0) = []
  | xList (n) = #"X" :: xList(n-1)
  
(*
    divideList l
    TYPE:    'a list -> 'a list list
    PRE:     5 divides length l with no remainder <=> length l mod 5 = 0
    POST:    List l split into sub-lists with length 5.
    EXAMPLE: 
        Divide the list [1,2,3,4,5,6,7,8,9,10]:
            divideList [1,2,3,4,5,6,7,8,9,10] = [[1,2,3,4,5],[6,7,8,9,10]]
        Divide the list [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]:
            divideList [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] = [[1,2,3,4,5],[6,7,8,9,10],[11,12,13,14,15]]
*)
(*  VARIANT: Length of l.
    TIME COMPLEXITY: Theta(n) always. *)
fun divideList ([]) = [] 
  | divideList (l)  = List.take(l,5) :: divideList(List.drop(l,5))

(*
    convertLetterToNum l
    TYPE:    char list -> int list
    PRE:     True
    POST:    List of integers that represent the ASCII-value minus 64 for each element with the same position in list l.
    EXAMPLE: convertLetterToNum [#"A", #"B", #"D"] = [1, 2, 4]
*)
(*  VARIANT: Length of l. 
    TIME COMPLEXITY: Theta(n) always. *)
fun convertLetterToNum([]) = []
  | convertLetterToNum(h::l) = (Char.ord(h) - 64) :: convertLetterToNum(l)
  
(*
    convertNumToLetter l
    TYPE:    char list -> int list
    PRE:     True
    POST:    List of chars where each element has an ASCII-value equal to the value of the element in the same position of list l plus 64.
    EXAMPLE: convertNumToLetter [1, 2, 3] = [#"A", #"B", #"C"]
*)
(*  VARIANT: Length of l. 
    TIME COMPLEXITY: Theta(n) always. *)
fun convertNumToLetter([])   = []
  | convertNumToLetter(h::l) = Char.chr(h + 64) :: convertNumToLetter(l)

(*
    listOp (f, l1, l2)
    TYPE:    (int * int -> int) * int list * int list -> int list
    PRE:     True
    POST:    Integer list, where each element represents the returned value of the function f for the elements at the same positions of lists l1 and l2.
             If the returned value from function f is below 1 it adds 26 to the value, if the returned value is above 26 then it subtracts 26 from the value.
    EXAMPLE: 
        Use addition on the lists [1,2,3,4] and [5,6,7,8]:
            listOp(op +, [1,2,3,4], [5,6,7,8]) = [6,8,10,12]
        Use subtraction on the lists [1,2,3,4] and [5,6,7,8]:
            listOp(op -, [1,2,3,4], [5,6,7,8]) = [22, 22, 22, 22]
        Use division on the lists [4,6,2,9] and [2,3,1,3]:
            listOp(op div, [4,6,2,9], [2,3,1,3]) = [2,2,2,3]
*)
(*  VARIANT: Length of l1 and l2. 
    TIME COMPLEXITY: Theta(n) always. *)
fun listOp (f, [], l2) = l2
  | listOp (f, l1, []) = l1
  | listOp (f, h1::l1, h2::l2) = 
    let
        val n = f(h1, h2)
    in
        (
            if n < 1 then 
                n + 26
            else if n > 26 then
                n - 26
            else 
                n
        ) :: listOp(f,l1,l2)
    end
        
(*
    switchOrder (j1, j2)
    TYPE:    joker * joker -> joker * joker
    PRE:     Jokers j1 and j2 can not be of the same value.
    POST:    Tuple where the jokers j1 and j2 has switched position.
    EXAMPLE:
        Switch places of the two jokers in (A,B):
            switchOrder(A,B) = (B,A)
        Switch places of the two jokers in (B,A):
            switchOrder(B,A) = (A,B)
*)
(*  TIME COMPLEXITY: Theta(1) always. *)
fun switchOrder (A,B) = (B,A)
  | switchOrder (B,A) = (A,B)

(*
   ===== END HELPER FUNCTIONS =====
*)

(*
    moveJokerA d
    TYPE:    deck -> deck
    PRE:     There are at least one card in the deck d besides the two jokers.
    POST:    The rearranged deck, where the joker A has taken one step according to the Solitaire cryptographic algorithm.
*)
(*  TIME COMPLEXITY: O(n) *)
fun moveJokerA (Deck(t, m, b, order)) =
    if queueSize(m) = 0 andalso order = (A,B) then
        Deck(t, m, b, (B,A))
    else if queueSize(m) >= 1 andalso order = (A,B) then
        Deck(enqueue(t, head(m)), dequeue(m), b, (A,B))
    else if queueSize(t) > 0 andalso queueSize(b) = 0 andalso order = (B,A) then
        Deck(enqueue(mkQueue(), head(t)), dequeue(t), m, (A,B))
    else if queueSize(b) > 0 andalso order = (B,A) then
        Deck(t, enqueue(m, head(b)), dequeue(b), (B,A))
    else
        raise Fail ("MoveJokerA has failed! Missing case for: t:" ^ Int.toString(queueSize(t)) ^ " m:" ^ Int.toString(queueSize(m)) ^ " b:" ^ Int.toString(queueSize(b)) ^ " order:" ^ (if order = (A,B) then "A,B" else "B,A"))

(*
    moveJokerB d
    TYPE:    deck -> deck
    PRE:     There are at least two cards in the deck besides the two jokers.
    POST:    The rearrenged deck, where the joker B has taken two steps according to the Solitaire cryptographic algorithm.
*)
(*  TIME COMPLEXITY: O(n) *)            
fun moveJokerB (Deck(t, m, b, order)) =
    if      queueSize(t) = 1 andalso queueSize(m) > 0 andalso queueSize(b) = 0 andalso order = (A,B) then (* A -> B, 1 card top, 0 cards bottom *)
        Deck(enqueue(mkQueue(), head(t)), b, m, order)
    else if queueSize(t) = 0 andalso queueSize(m) > 0 andalso queueSize(b) = 0 andalso order = (A,B) then (* A -> B, 0 cards top, atleast one card between, 0 cards bottom *)
        Deck(t, enqueue(mkQueue(), head(m)), dequeue(m), order)
    else if queueSize(t) > 1                          andalso queueSize(b) = 0 andalso order = (A,B) then (* A -> B, >1 cards top, 0 cards bottom *)
        let
            val t2 = dequeue(t)
            val t3 = dequeue(t2)
            val h1 = head(t)
            val h2 = head(t2)
        in
            Deck(enqueue(enqueue(mkQueue(), h1), h2), t3, m, (B,A))
        end
    else if queueSize(t) = 1 andalso queueSize(m) > 2 andalso queueSize(b) = 1 andalso order = (A,B) then (* A -> B, 1 card top, >2 cards between, 1 card bottom *)
        Deck(t, mkQueue(), enqueue(m, head(b)), (B,A))
    else if queueSize(t) = 0 andalso queueSize(m) > 1 andalso queueSize(b) = 1 andalso order = (A,B) then (* A -> B, 0 cards top, >1 cards between, 1 card bottom *)
        Deck(t, mkQueue(), enqueue(m, head(b)), order)
    else if queueSize(t) > 1                          andalso queueSize(b) = 1 andalso order = (A,B) then (* A -> B, >1 cards top, 1 card bottom *)
        Deck(enqueue(mkQueue(), head(t)), dequeue(t), enqueue(m, head(b)), (B,A))
    else if                                                   queueSize(b) > 1 andalso order = (A,B) then (* A -> B, >1 cards bottom *)
        let
            val b2 = dequeue(b)
            val b3 = dequeue(b2)
            val h1 = head(b)
            val h2 = head(b2)
        in
            Deck(t, enqueue(enqueue(m, h1), h2), b3, order)
        end
    else if queueSize(t) > 1 andalso queueSize(m) = 0 andalso queueSize(b) = 0 andalso order = (B,A) then (* B -> A, >1 cards top, 0 cards between, 0 cards bottom *)
        Deck(enqueue(mkQueue(), head(t)), dequeue(t), mkQueue(), order)
    else if queueSize(t) > 1 andalso queueSize(m) = 1 andalso queueSize(b) = 0 andalso order = (B,A) then (* B -> A, >1 cards top, 1 card between, 0 cards bottom *)
        Deck(enqueue(t, head(m)), mkQueue(), mkQueue(), (A,B))
    else if                          queueSize(m) = 0 andalso queueSize(b) > 0 andalso order = (B,A) then (* B -> A, 0 cards between, >0 cards bottom *)
        Deck(t, enqueue(m, head(b)), dequeue(b), (A,B))
    else if                          queueSize(m) = 1                          andalso order = (B,A) then (* B -> A, 1 card between *)
        Deck(enqueue(t, head(m)), mkQueue(), b, (A,B))
    else if                          queueSize(m) > 1                          andalso order = (B,A) then (* B -> A, >1 cards between *)
        let
            val m2 = dequeue(m)
            val m3 = dequeue(m2)
            val h1 = head(m)
            val h2 = head(m2)
        in
            Deck(enqueue(enqueue(t, h1), h2), m3, b, order)
        end
    else
        raise Fail ("MoveJokerB has failed! Missing case for: t:" ^ Int.toString(queueSize(t)) ^ " m:" ^ Int.toString(queueSize(m)) ^ " b:" ^ Int.toString(queueSize(b)) ^ " order:" ^ (if order = (A,B) then "A,B" else "B,A"))
    
(*
    tripleCut d
    TYPE:    deck -> deck
    PRE:     True
    POST:    Deck d, where the lists top and bottom has changed place with each other.
*)
(*  TIME COMPLEXITY: Theta(1) always. *)
fun tripleCut (Deck(top, middle, bottom, order)) = Deck(bottom, middle, top, order)
    
(* 
    countCut d
    TYPE:   deck -> deck
    PRE:    True
    POST:   Deck d, where the cards have been rearranged according to the count cut move in the Solitaire cryptographic algorithm.
*)
(*  TIME COMPLEXITY: O(n) *)
fun countCut (d as (Deck(t, m, b, order))) = 
    let
        val n = if isEmpty(b) then 53 else butt(b) (* If the bottom queue is empty then a joker is the bottom card *)
                
        val joker1 = queueSize(t) + 1
        val joker2 = joker1 + queueSize(m) + 1
    in
        if isEmpty(b) then (* Performing a count cut where the bottom card is a joker would result in the same deck *)
            d
        else if n < joker1 then
            let
                val (queue, cards) = extract(t, n, [])
            in
                Deck(queue, m, enqueue(enqueueList(dequeueButt(b), cards), butt(b)), order)
            end
        else if n < joker2 then
            let
                val (queue, cards) = extract(m, n - joker1, [])
            in
                Deck(queue, merge(dequeueButt(b), t), enqueue(enqueueList(mkQueue(), cards), butt(b)), switchOrder(order))
            end
        else
            let
                val (queue, cards) = extract(dequeueButt(b), n - joker2, [])
            in
                Deck(merge(queue, t), m, enqueue(enqueueList(mkQueue(), cards), butt(b)), order)
            end
    end
    
(*
    outputLetter d
    TYPE:   deck -> deck
    PRE:    True
    POST:   The n'th value in the deck d converted to its respective letter, where n is defined by the value at the top of the deck.
*)
(*  TIME COMPLEXITY: O(n) *)
fun outputletter(d as (Deck(t, m, b, order))) = 
    let
        val value = if isEmpty(t) then 53 else head(t)
        
        fun convert (n) = 
            let
                val n = n mod 26
            in
                if n = 0 then
                    #"Z"
                else
                    Char.chr(n + 64)
            end
            
        val joker1 = queueSize(t) + 1
        val joker2 = joker1 + queueSize(m) + 1
    in
        if value = (joker1 - 1) orelse value = (joker2 - 1) then 
            #"?"
        else if value >= joker2 then
            convert(nth(b, value - joker2))
        else if value >= joker1 then
            convert(nth(m, value - joker1))
        else
            convert(nth(t, value))
    end

(* 
    keystream n
    TYPE:   int -> char list list
    PRE:    n >= 0
    POST:   A 2dimensional char list for usage when encrypting/decrypting according to the Solitaire cryptographic algorithm.
*)
(*  TIME COMPLEXITY: O(n) *)
fun keystream (n) =
    let
        val sortedDeck = makeDeck([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52])
        
        fun iterate (_, 0) = []
          | iterate (d, n) = 
            let
                val newDeck = countCut(tripleCut(moveJokerB(moveJokerA(d))))
                val out = outputletter(newDeck)
            in
                if out = #"?" then
                    iterate(newDeck, n)
                else
                    out::iterate(newDeck, n-1)
            end
    in
        iterate(sortedDeck, n)
    end
    
(*
    preprocess s
    TYPE:    string -> char list list
    PRE:     True
    POST:    List of char lists, where each char-list is a five character section of the letters in s. 
             If size s mod 5 != 0 then X's has been appended until this is true.
    EXAMPLE: 
        Preprocess the string "foo":
            preprocess "foo" =  [[#"F", #"O", #"O", #"X", #"X"]]
*)
(* TIME COMPLEXITY: Theta(n) *)
fun preprocess s = 
    let
        val upper   = (List.map Char.toUpper) (explode(s)) (* Converts the string s to a char-list with only upper-case characters. *)
        val cleaned = (List.filter Char.isAlpha) upper     (* Cleans the list upper from any non-letter characters. *)
        val return  = divideList(cleaned @ xList((5 - (length cleaned mod 5)) mod 5))
    in
        return
    end
    
(*
    crypt (f, l, ks)
    TYPE:    (int * int -> int) * char list list * char list list -> char list list
    PRE:     f is one of the operators + or - to specify encryption or decryption, l contains the char groups to be encrypted/decrypted, ks is the key stream to use in the algorithm.
    POST:    Char list list encrypted/decrypted according to the Solitaire cryptographic algorithm.
    EXAMPLE:
        Encrypt the two char groups [[#"L", #"I", #"V", #"E", #"L"], [#"O", #"N", #"G", #"X", #"X"]] with the key stream [[#"D", #"W", #"J", #"X", #"H"], [#"Y", #"R", #"F", #"D", #"G"]]:
            crypt(op +, [[#"L", #"I", #"V", #"E", #"L"], [#"O", #"N", #"G", #"X", #"X"]], [[#"D", #"W", #"J", #"X", #"H"], [#"Y", #"R", #"F", #"D", #"G"]]) = [[#"P", #"F", #"F", #"C", #"T"], [#"N", #"F", #"M", #"B", #"E"]]
        Decrypt the two char groups from example above, with the same key stream:
            crypt(op -, [[#"P", #"F", #"F", #"C", #"T"], [#"N", #"F", #"M", #"B", #"E"]], [[#"D", #"W", #"J", #"X", #"H"], [#"Y", #"R", #"F", #"D", #"G"]]) = [[#"L", #"I", #"V", #"E", #"L"], [#"O", #"N", #"G", #"X", #"X"]]
*)
(*  VARIANT: Length of the shortest of l and ks.
    TIME COMPLEXITY: Theta(n) *)
fun crypt (_, [],_) = []
  | crypt (_, _,[]) = []
  | crypt (f, h::l, hk::ks) = convertNumToLetter(listOp(f, convertLetterToNum(h), convertLetterToNum(hk))) :: crypt(f, l, ks)

(*
    encrypt s
    TYPE:    char list list -> char list list
    PRE:     True
    POST:    Char list list that is the encrypted version of s according to the Solitaire cryptographic algorithm.
    EXAMPLE:
        Encrypt the string "Hello there":
            encrypt "Hello there" = [[#"L", #"B", #"V", #"J", #"W"], [#"S", #"Z", #"K", #"V", #"L"]]
*)
(*  TIME COMPLEXITY: Theta(n) *)
fun encrypt (l) = crypt(op +, l, divideList(keystream(length l * 5)))

(*
    decrypt l
    TYPE:    char list list -> char list list
    PRE:     Every sub-list of l has a length of 5.
    POST:    Char list list that is the decrypted version of l according to the Solitaire cryptographic algorithm.
    EXAMPLE:
        Decrypt the list list [[#"L", #"B", #"V", #"J", #"W"], [#"S", #"Z", #"K", #"V", #"L"]]:
            decrypt [[#"L", #"B", #"V", #"J", #"W"], [#"S", #"Z", #"K", #"V", #"L"]] = [[#"H", #"E", #"L", #"L", #"O"], [#"T", #"H", #"E", #"R", #"E"]]
*)
(*  TIME COMPLEXITY: Theta(n) *)
fun decrypt (l) = crypt(op -, l, divideList(keystream(length l * 5)))
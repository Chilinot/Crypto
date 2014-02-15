fun test n = 
    let
        fun test 1 = 
            let
                val q = mkQueue()
                val e1 = enqueue(q, 12)
            in
                isEmpty(q) andalso
                queueSize(e1) = 1 andalso
                head(e1) = 12 andalso
                butt(e1) = 12 andalso
                nth(e1, 0) = 12
            end
            
          | test 2 = 
            let
                val q = enqueue(mkQueue(), 12)
                val (qx, lx) = extract(q, 1, [])
            in
                isEmpty(qx) andalso
                length lx = 1 andalso
                lx = [12]
            end
            
          | test 3 =
            let
                val q = enqueueList(mkQueue(), [1,2,3,4,5,6,7,8])
                val q2 = normalize(q)
                val q3 = merge(q2, q)
                val (q4, l) = extract(q3, queueSize(q3), [])
                val q5 = dequeueButt(q3)
            in
                (queueSize(q) * 2) = queueSize(q3) andalso
                queueSize(q2) = queueSize(q) andalso
                head(q3) = 1 andalso
                butt(q3) = 8 andalso
                l = [1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8] andalso
                isEmpty(q4) andalso
                nth(q3, 9) = 2 andalso
                butt(q5) = 7
            end
    in
        (n, test n)
    end
    
fun listToString([]) = ""
  | listToString(x::l) = Int.toString(x) ^ " , " ^ listToString(l) *)
  
(* val debug = print(
            "\nDebug-outputletter-deck: \n" ^ 
            "Order: " ^ (if order = (A,B) then "A,B" else "B,A") ^ "\n" ^ 
            "Top: " ^ listToString(#2(extract(t, queueSize(t), []))) ^ "\n" ^
            "Mid: " ^ listToString(#2(extract(m, queueSize(m), []))) ^ "\n" ^
            "Bot: " ^ listToString(#2(extract(b, queueSize(b), []))) ^ "\n" ^
            "Totalsize:" ^ Int.toString(queueSize(t) + queueSize(m) + queueSize(b)) ^ " t:" ^ Int.toString(queueSize(t)) ^ " m:" ^ Int.toString(queueSize(m)) ^ " b:" ^ Int.toString(queueSize(b)) ^ "\n") *)
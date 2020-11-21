------------------------------ MODULE termDet ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, Naturals
CONSTANT N, MaxT
ASSUME N \in Nat \ {0,1}
Procs == 1..N

(*
--algorithm termDet {
  variables
  chan = [n \in 0..N |-> <<>>];
 
 

  macro send(des, msg) {
      chan[des] := Append(chan[des], msg);
      }

  macro receive(msg) {
      when Len(chan[self]) > 0;
      msg := Head(chan[self]);
      chan[self] := Tail(chan[self]);
  }
   
  fair process (j \in Procs)
  variables
  T=0;
  m = 0;
  active=TRUE;
  outc = [n \in 0..N |-> 0];
  inc = 0;
  {
   P:while (T<MaxT){  
        T := T+1;
        either
               {
               when active;
                   with (des \in Procs)
                       {
                        send(des,m);
                        outc[des]:=outc[des]+1;
                       }
               };
        or
              {
               receive(m);
               active := TRUE;
               inc := inc + 1;
               
               };
        or
              {
                when active;                  
                   send(0,<<self,inc,outc>>);
                   active := FALSE;
                   
               };
      }
  }


  fair process (d \in {0}) \* Detector process
  variables
  done=FALSE;
  msg= <<>>;
  notified={};
  outS= [n \in 1..N |-> 0];
  inS = [n \in 1..N |-> 0];
  
  x = 0; \* for iterating the outS tuple
  sender = 0; \* to store sender id
  
  {
   D: while(~done) {
        receive(msg);
        sender := msg[1];
        inS[sender] := msg[2];
        notified := notified \union {sender};
        
        x := 1;
        A: while (x <= N)
            {
                outS[x] := outS[x] + msg[3][x]; 
                x := x+1;  
            };
        
        
            if ((\A i \in Procs: i \in notified) /\ (\A u \in Procs: inS[u] = outS[u]))
                {done := TRUE;
                }
                
            else 
                done := FALSE;
                
        
    }
  }

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ca3244b193251f7de283f20f19379798
VARIABLES chan, pc, T, m, active, outc, inc, done, msg, notified, outS, inS, 
          x, sender

vars == << chan, pc, T, m, active, outc, inc, done, msg, notified, outS, inS, 
           x, sender >>

ProcSet == (Procs) \cup ({0})

Init == (* Global variables *)
        /\ chan = [n \in 0..N |-> <<>>]
        (* Process j *)
        /\ T = [self \in Procs |-> 0]
        /\ m = [self \in Procs |-> 0]
        /\ active = [self \in Procs |-> TRUE]
        /\ outc = [self \in Procs |-> [n \in 0..N |-> 0]]
        /\ inc = [self \in Procs |-> 0]
        (* Process d *)
        /\ done = [self \in {0} |-> FALSE]
        /\ msg = [self \in {0} |-> <<>>]
        /\ notified = [self \in {0} |-> {}]
        /\ outS = [self \in {0} |-> [n \in 1..N |-> 0]]
        /\ inS = [self \in {0} |-> [n \in 1..N |-> 0]]
        /\ x = [self \in {0} |-> 0]
        /\ sender = [self \in {0} |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "P"
                                        [] self \in {0} -> "D"]

P(self) == /\ pc[self] = "P"
           /\ IF T[self]<MaxT
                 THEN /\ T' = [T EXCEPT ![self] = T[self]+1]
                      /\ \/ /\ active[self]
                            /\ \E des \in Procs:
                                 /\ chan' = [chan EXCEPT ![des] = Append(chan[des], m[self])]
                                 /\ outc' = [outc EXCEPT ![self][des] = outc[self][des]+1]
                            /\ UNCHANGED <<m, active, inc>>
                         \/ /\ Len(chan[self]) > 0
                            /\ m' = [m EXCEPT ![self] = Head(chan[self])]
                            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                            /\ active' = [active EXCEPT ![self] = TRUE]
                            /\ inc' = [inc EXCEPT ![self] = inc[self] + 1]
                            /\ outc' = outc
                         \/ /\ active[self]
                            /\ chan' = [chan EXCEPT ![0] = Append(chan[0], (<<self,inc[self],outc[self]>>))]
                            /\ active' = [active EXCEPT ![self] = FALSE]
                            /\ UNCHANGED <<m, outc, inc>>
                      /\ pc' = [pc EXCEPT ![self] = "P"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, T, m, active, outc, inc >>
           /\ UNCHANGED << done, msg, notified, outS, inS, x, sender >>

j(self) == P(self)

D(self) == /\ pc[self] = "D"
           /\ IF ~done[self]
                 THEN /\ Len(chan[self]) > 0
                      /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
                      /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                      /\ sender' = [sender EXCEPT ![self] = msg'[self][1]]
                      /\ inS' = [inS EXCEPT ![self][sender'[self]] = msg'[self][2]]
                      /\ notified' = [notified EXCEPT ![self] = notified[self] \union {sender'[self]}]
                      /\ x' = [x EXCEPT ![self] = 1]
                      /\ pc' = [pc EXCEPT ![self] = "A"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, msg, notified, inS, x, sender >>
           /\ UNCHANGED << T, m, active, outc, inc, done, outS >>

A(self) == /\ pc[self] = "A"
           /\ IF x[self] <= N
                 THEN /\ outS' = [outS EXCEPT ![self][x[self]] = outS[self][x[self]] + msg[self][3][x[self]]]
                      /\ x' = [x EXCEPT ![self] = x[self]+1]
                      /\ pc' = [pc EXCEPT ![self] = "A"]
                      /\ done' = done
                 ELSE /\ IF (\A i \in Procs: i \in notified[self]) /\ (\A u \in Procs: inS[self][u] = outS[self][u])
                            THEN /\ done' = [done EXCEPT ![self] = TRUE]
                            ELSE /\ done' = [done EXCEPT ![self] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "D"]
                      /\ UNCHANGED << outS, x >>
           /\ UNCHANGED << chan, T, m, active, outc, inc, msg, notified, inS, 
                           sender >>

d(self) == D(self) \/ A(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: d(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(d(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e3f01851f6dcd566efd0415f314dbfea
Safety == done[0] => (\A i \in Procs: active[i]=FALSE) /\  (\A u \in 0..N: chan[u] = <<>>)
Progress == ((\A i \in Procs: active[i]=FALSE) /\  (\A u \in 0..N: chan[u] = <<>>)) ~> (done[0])
 
=============================================================================
\* Project Team: Harita Ramesh Babu (haritara), Krithika Raj Dorai Raj (kdoraira)


\* Modification History
\* Last modified Fri Nov 13 21:10:24 EST 2020 by Krithika
\* Created Fri Nov 13 14:07:09 EST 2020 by Krithika

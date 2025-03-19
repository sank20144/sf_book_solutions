Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
  
  Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
  
  Example test_next_working_day:
    (next_working_day (next_working_day saturday)) = tuesday.
   
  Proof. simpl. reflexivity. Qed.
  
  From Coq Require Export String.
  
  Inductive bool: Type:=
  | true
  | false.
  
  Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.
  
  Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.
  
  Definition andb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.
  
  Definition andb' (b1:bool) (b2:bool) : bool :=
    if b1 then b2
    else false.
  
  Definition nandb (b1:bool) (b2:bool) : bool :=
    if andb' b1 b2 then false
    else true.
    
  Example test_nandb1: (nandb true false) = true.
  Proof. simpl. reflexivity. Qed.
  
  Example test_nandb2: (nandb false false) = true.
  Proof. simpl. reflexivity. Qed.
  
  Example test_nandb3: (nandb false true) = true.
  Proof. simpl. reflexivity. Qed.
  
  Example test_nandb4: (nandb true true) = false.
  Proof. simpl. reflexivity. Qed.
  
  Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
    if andb' b1 b2 then b3
    else false.
    
  Example test_andb31: (andb3 true true true) = true.
  Proof. simpl. reflexivity. Qed.
  
  Example test_andb32: (andb3 false true true) = false.
  Proof. simpl. reflexivity. Qed.
  
  Example test_andb33: (andb3 true false true) = false.
  Proof. simpl. reflexivity. Qed.
  
  Example test_andb34: (andb3 true true false) = false.  
  Proof. simpl. reflexivity. Qed.
  
  Check true.
  Check bool.
  Check nandb.
  Check andb'.
  Check andb3.
  Check test_nandb1.
  Check true : bool.

  Check monday: day.
  
  Inductive rgb : Type :=
    | red
    | green
    | blue.
    
  Inductive color : Type :=
    | black
    | white
    | primary (p : rgb).
    
  Definition monochrome (c : color) : bool := 
    match c with
      | black => true
      | white => true
      | primary p => false
      end.
      
  Definition isred (c: color) : bool :=
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.
  
  Module Playground.
    Definition foo : rgb := blue.
  End Playground.
  
  Definition foo : bool := true.
  
  Check Playground.foo : rgb.
  Check foo : bool.
  
  Inductive bit : Type := 
    | B1
    | B0.
  
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).
    
  Check (bits B1 B0 B1 B1).
  
  Definition all_zero (nb: nybble) : bool :=
    match nb with
      | (bits B0 B0 B0 B0) => true
      | (bits _ _ _ _) => false
    end.
  
  Compute (all_zero (bits B1 B0 B1 B1)).
  
  Compute (all_zero (bits B0 B0 B0 B0)).
  
  Module NatPlayground.
  
    Inductive nat : Type :=
      | O
      | S (n : nat).
    Definition pred (n : nat) : nat :=
      match n with
      | O => O
      | S n' => n'
      end.
    
    Compute pred (S(S(S O))).
   End NatPlayground.
   
   Check (S(S(S O))).
   
   Definition minustwo (n : nat) : nat := 
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.
    
   Compute minustwo (S(S(S O))).
   Compute minustwo 4.
   
   Check S.
   
   Fixpoint even (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.
   
   Check negb.
   
   Definition odd (n:nat) : bool :=
    negb (even n).
    
   Example test_odd1: odd 1 = true.
   Proof. simpl. reflexivity. Qed.
   
   Example test_odd2: odd 4 = false.
   Proof. simpl. reflexivity. Qed.
   
   Module NatPlayground2.
   
   Fixpoint plus (n:nat) (m:nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
    
    Compute (plus 3 2).
    
   Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
    end.
   
  Fixpoint mult (n m:nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
    
   Example test_mult1: (mult 3 3) = 9.
   Proof. simpl. reflexivity. Qed.
   
   End NatPlayground2.
   
   Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.
    
    Example test_exp1: (exp 2 2) = 4.
    Proof. simpl. reflexivity. Qed.
    
    Fixpoint factorial (n:nat) : nat :=
      match n with
      | O => S O
      | S p' => mult n (factorial p')
      end.
      
    Example test_factorial1: (factorial 3) = 6.
    Proof. simpl. reflexivity. Qed.
    
    Example test_factorial2: (factorial 5) = (mult 10 12).
    Proof. simpl. reflexivity. Qed.
    
    Notation "x + y" := (plus x y) 
    (at level 50, left associativity) : nat_scope.
    Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
    Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
    Check ((0 + 1) + 1) : nat.
    
    Fixpoint eqb (n m : nat) : bool :=
      match n with
      | O => match m with
              | O => true
              | S m' => false
              end
      | S n' => match m with 
              | O => false
              | S m' => eqb n' m'
              end
      end.
      
      Fixpoint leb (n m : nat) : bool :=
        match n with
        | O => true
        | S n' => 
                match m with
                | O => false
                | S m' => leb n' m'
                end
        end.
        
    Example test_leb1: leb 2 2 = true.
    Proof. simpl. reflexivity. Qed.
    Example test_leb2: leb 2 4 = true.
    Proof. simpl. reflexivity. Qed.
    Example test_leb3: leb 4 2 = false.
    Proof. simpl. reflexivity. Qed.
    
  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
  Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
  
  Example test_leb3': (4 <=? 2) = false.
  Proof. simpl. reflexivity. Qed.
  
  Fixpoint ltb (n m : nat) : bool :=
    match n with
    | O => match m with
          | O => false
          | S m' => true
          end
    | S n' => match m with
          | O => false
          | S m' => ltb n' m'
          end
    end.
    
  Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
  
  Example test_ltb1: (ltb 2 2) = false.
  Proof. simpl. reflexivity. Qed.
  
  Example test_ltb2: (ltb 2 4) = true.
  Proof. simpl. reflexivity. Qed.
  
  Example test_ltb3: (ltb 4 2) = false.
  Proof. simpl. reflexivity. Qed.
  
  Theorem plus_0_n : forall n : nat, 0 + n = n.
  Proof.
    intros n. reflexivity. Qed.
  
  Theorem plus_1_l : forall n : nat, 1 + n = S n.
  Proof.
    intros n. simpl. reflexivity. Qed.
  
  Theorem mult_0_l : forall n: nat, 0 * n = 0.
  Proof.
    intros n. simpl. reflexivity. Qed.
    
  Theorem plus_id_example: forall n m:nat, 
  n = m -> 
  n + n = m + m.
  Proof.
    intros n m.
    intros H.
    rewrite <- H.
    simpl.
    reflexivity.
    Qed.
  
  Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
  Proof.
    intros n m o.
    intros H.
    intros H2.
    rewrite H.
    rewrite H2.
    reflexivity.
    Qed.
    
  Check mult_n_O.
    
  Check mult_n_Sm.
  
  Theorem mult_n_0_m_0 : forall p q : nat,
  (p * O) + (q * O) = O.
  Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    reflexivity. Qed.
  
  Check mult_n_Sm.
  
  Theorem mult_n_1 : forall p: nat,
  p * 1 = p.
  Proof.
    intros p.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl.
    reflexivity. Qed.
    
  Theorem plus_1_neq_0_firsttry : forall n : nat,
    (n + 1) =? 0 = false.
  Proof.
    intros n.
    simpl.
  Abort.
  
  Theorem plus_1_neq_0: forall n: nat,
  (n + 1) =? 0 = false.
  Proof. 
    intros n.
    destruct n as  [| n'] eqn:E.
    - simpl.
      reflexivity.
    - reflexivity. Qed.
    
  Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
  Proof.
    intros b. destruct b eqn:E.
    - simpl. reflexivity.
    - reflexivity. Qed.
    
  Theorem andb_commutative : forall b c , andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + simpl. reflexivity.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity. Qed.
      
  Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
  Proof.
    intros b c.
    - destruct c eqn:Eb.
      + intros H. reflexivity.
      + intros H1. rewrite <- H1. destruct b. simpl. reflexivity. reflexivity. Qed.
      
  Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
  Proof.
    intros [|n].
      - simpl. reflexivity.
      - reflexivity. Qed.
  
  Theorem andb_commutative'' : forall b c, andb b c = andb c b.
    Proof.
      intros [] [].
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity. Qed.
      
  Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
  Proof.
    intros [].
    - reflexivity.
    - reflexivity. Qed.
    
  Check negb.
  Theorem identity_fn_applied_twice : 
    forall (f: bool -> bool),
    (forall (x : bool), f x = x) -> forall (b: bool), f (f b) = b.
    Proof.
      intros f x b. destruct b. rewrite x. rewrite x. reflexivity.
      rewrite x. rewrite x. reflexivity. Qed.
      
  Theorem negation_fn_applied_twice :
    forall (f: bool -> bool),
    (forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
    Proof.
      intros f x b. destruct b. rewrite x. rewrite x. rewrite negb_involutive. reflexivity.
      rewrite x. rewrite x. rewrite negb_involutive. reflexivity. Qed.
      
  Theorem andb_eq_orb : forall (b c : bool), (andb b c = orb b c) -> b = c.
  Proof.
    intros b c.
    destruct b, c. reflexivity. intros H. inversion H. intros H. inversion H. reflexivity. Qed.
     
  Module LateDays.
    Inductive letter : Type :=
      | A | B | C | D | F.
      
    Inductive modifier: Type :=
      | Plus | Natural | Minus.
    
    Inductive grade : Type :=
      Grade (l:letter) (m:modifier).
      
    Inductive comparison : Type :=
      | Eq
      | Lt
      | Gt.
      
    Definition letter_comparison (l1 l2 : letter) : comparison :=
      match l1, l2 with
      | A, A => Eq
      | A, _ => Gt
      | B, A => Lt
      | B, B => Eq
      | B, _ => Gt
      | C, (A | B) => Lt
      | C, C => Eq
      | C, _ => Gt
      | D, (A | B | C) => Lt
      | D, D => Eq
      | D, _ => Gt
      | F, F => Eq
      | F, _ => Lt
      end.
      
      Compute letter_comparison B A.
      Compute letter_comparison A F.
      
      Theorem letter_comparison_Eq : forall l, letter_comparison l l = Eq.
      Proof.
      intros l. destruct l. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. Qed.
      
      Definition modifier_comparison (m1 m2 : modifier) : comparison :=
        match m1, m2 with
        | Plus, Plus => Eq
        | Plus, _ => Gt
        | Natural, Plus => Lt
        | Natural, Natural => Eq
        | Natural, _ => Gt
        | Minus, Minus => Eq
        | Minus, _ => Lt
        end.
        
        
        Definition grade_comparison (g1 g2 : grade) : comparison :=
          match g1, g2 with
            | Grade letter' modifier', Grade letter'' modifier'' => 
                        match letter_comparison letter' letter'' with
                        | Eq => modifier_comparison modifier' modifier''
                        | Gt => Gt
                        | Lt => Lt
                        end
             
           end.
           
       Example test_grade_comparison1 : (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
       Proof. simpl. reflexivity. Qed.
           
       Example test_grade_comparison2 : (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
       Proof. simpl. reflexivity. Qed.
       
       Example test_grade_comparison3 : (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
       Proof. simpl. reflexivity. Qed.
       
       Example test_grade_comparison4 : (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
       Proof. simpl. reflexivity. Qed.
       
       Definition lower_letter (l : letter) : letter :=
        match l with
        | A => B
        | B => C
        | C => D
        | D => F
        | F => F
        end.
        
        Theorem lower_letter_lowers:
        forall (l: letter), 
          letter_comparison F l = Lt -> letter_comparison (lower_letter l) l = Lt.
        Proof.
          intros l. destruct l.
          - simpl. reflexivity.
          - simpl. reflexivity.
          - simpl. reflexivity.
          - simpl. reflexivity.
          - simpl. intros h. rewrite h. reflexivity. Qed.
          
        Definition lower_grade (g: grade) : grade :=
          match g with
          | Grade F Minus => Grade F Minus
          | Grade l' m' => match m' with
                        | Plus => Grade l' Natural
                        | Natural => Grade l' Minus
                        | Minus => Grade (lower_letter l') Plus
                        end
          end.
        
        Example lower_grade_A_plus :
          lower_grade (Grade A Plus) = (Grade A Natural).
          Proof. simpl. reflexivity. Qed.
          
        Example lower_grade_A_Natural :
          lower_grade (Grade A Natural) = (Grade A Minus).
          Proof. reflexivity. Qed.
          
        Example lower_grade_A_Minus :
          lower_grade (Grade A Minus) = (Grade B Plus).
          Proof. reflexivity. Qed.
         
        Example lower_grade_B_Plus :
          lower_grade (Grade B Plus) = (Grade B Natural).
          Proof. reflexivity. Qed.
          
        Example lower_grade_F_Natural :
          lower_grade (Grade F Natural) = (Grade F Minus).
          Proof. reflexivity. Qed.
        
        Example Llower_grade_twice : 
          lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
          Proof. simpl. reflexivity. Qed.
          
End LateDays.
 
    
  
  
    
    
    
  
    
  
      
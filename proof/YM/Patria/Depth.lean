import YM.Patria.Tucks
import YM.Patria.Icon
import YM.Massive.RG.History
/-! Recover step iterations including insertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
variable {S:Scheme}{r:Side}{N d:ℕ}
-- Stencils unspecified powers yet
variable (A:Run S N r 6)(hA:A.Actual)
def ratioTo (S:Scheme)(N m:ℕ):= (S.ratio N).val / (S.ratio m).val
local notation "Q" => ratioTo S N
variable {m i:ℕ}
abbrev stitch (S:Scheme)(r:Side)(m:ℕ):=coarse (S.step m) S.choices (S.sides_next r m)
local notation "H"=> S.side r
@[simp] lemma centreN : Q N=1:=Nat.div_self (S.ratio N).property
lemma factorize (h:m≤N): (S.ratio N).val = (S.ratio m).val * ratioTo S N m:=by
    induction h using Nat.decreasingInduction with
    | self=> rw [centreN,mul_one]
    | of_succ m h ih=>
       have hg : (S.ratio N).val=(S.ratio m).val*((S.step m).L.val*Q (m+1)):=by rw [Scheme.ratio, PNat.mul_coe,Nat.mul_assoc] at ih; exact ih
       unfold ratioTo; apply Eq.symm; refine Nat.mul_div_cancel' ?_; exact ⟨_,hg⟩
lemma step_factor (h : m<N): Q m=(S.step m).L.val*Q (m+1):=by
    have hh : (S.ratio m).val*Q m=(S.ratio m).val*((S.step m).L.val*Q (m+1)):= ((factorize (S:=S) h.le)).symm.trans ((factorize (S:=S) h).trans (by rw [Scheme.ratio,PNat.mul_coe,Nat.mul_assoc])); exact Nat.eq_of_mul_eq_mul_left (S.ratio m).property hh
lemma odd_to(h:m≤N): Odd (Q m):=by induction h using Nat.decreasingInduction with|self=>rw [centreN]; exact odd_one|of_succ m h ih=>rw [step_factor h]; exact (S.step m).odd.mul ih
abbrev AllAt (A:Run S N r 6) (m:ℕ):= S.toStop r A.β A.w (F:=6) N m
local notation "TX"=> AllAt A
abbrev region (A:Run S N r 6) :=A.regulator.density
local notation "Sn" =>A.regulator.density
lemma origin : TX N=LinearMap.id:=S.entrance r ..
lemma route(X: Insertion (H N) 6)(h:m<N): ⇑(TX m X)= A.block m (TX (m+1) X):=by rw [S.next r _ _ h]; rfl
lemma holding (X:Insertion (H N) 6)(a:ℕ) : A.Carried (fun i=> ⇑(TX i X)) a:= ⟨fun {i} _ _=>Continuous.integrable_of_hasCompactSupport (ContinuousMap.continuous _) (HasCompactSupport.of_compactSpace _),fun {i} _ _=>Transfer.soften_pay _ _ (ContinuousMap.continuous _),fun {_} _ h=>route A X h⟩ -- implicit {i}
include hA
lemma pier (hi:i ≤N): A.density i=TX i Sn:= by
    induction hi using Nat.decreasingInduction with|self=> rw [hA.start, origin,LinearMap.id_apply] | of_succ m h ih=> rw [route A Sn h,hA.travels.eqn (Nat.zero_le _) h,ih]
-- on unit
lemma gym (m:ℕ) (X: Insertion (H (m+1)) 6): ⇑(S.send r A.β A.w m X)=TorusPCAC.block (stitch S r m) (A.β (m+1)) (A.w m) X:= step_brute .. -- hA unused remove
omit hA
variable (s:Signed)(u:FlavorTorus)(a:Axis)(p:EuPin)
local notation "κ"=> TorusPCAC.block
open Exposure
variable (X Y : Insertion (S.side r N) 6)
lemma step_shift (m:ℕ)(b:Cover)(X: Density (H (m+1)) 6)(hx:Continuous X): march b (A.block m X)= A.block m (march ((S.step m).L.val • b) X):=by unfold Run.block; rw [step_brute,step_brute]; exact move_travel (stitch S r m) X (S.admissible m) _ _ hx b -- supply hx hc
-- cohesive
lemma moving (Φ:(c:Side) → Density c 6→ Density c 6)(h:∀ m:ℕ,∀ x:Insertion (S.side r (m+1)) 6, Φ _ (A.block m x)= A.block m (Φ _ x))(he: Φ _ X=Y)(hi:i≤N): Φ _ (TX i X)= TX i Y:=by
    induction hi using Nat.decreasingInduction with|self=> rw [origin]; exact he| of_succ m hg ih=> rw [route A X hg, route A Y hg,h,ih]
lemma journey (b: Cover)(hi:i≤N)(hp:march (Q i • b) X= Y): march b (TX i X)=TX i Y:=by induction hi using Nat.decreasingInduction generalizing b with|self=> rw [origin]; simpa [centreN] using hp|of_succ m h ih=> rw [route A X h,route A Y h, step_shift A m b (TX (m+1) X) (ContinuousMap.continuous _),ih]; rwa [step_factor h,Nat.mul_comm,mul_smul] at hp
lemma pin_moves (hp:p.Lifts s)(he:Action.pin p s X=Y)(hi:i≤N):Action.pin p s (TX i X)=TX i Y:=by refine moving A _ _ (fun _=>Action.pin p s) (fun m x=> ?_) he hi; unfold Run.block; rw [step_brute,step_brute]; exact pin_travel (stitch S r m) _ s p hp (S.admissible m) _ _ (ContinuousMap.continuous x)
lemma eyes (he:Action.adj a X=Y)(hi:i≤N):Action.adj a (TX i X)=TX i Y:=by refine moving A _ _ (fun _=> Action.adj a) (fun m x=>?_) he hi; unfold Run.block; rw [step_brute,step_brute]; exact eye_shift (stitch S r m) _ a (S.admissible m) _ _ (ContinuousMap.continuous x)
lemma chargery (he:Action.charge X=Y)(hi:i≤N):Action.charge (TX i X)=TX i Y:=by refine moving A _ _ (fun _=> Action.charge) (fun m x=>?_) he hi; unfold Run.block; rw [step_brute,step_brute]; exact charge_shift (stitch S r m) _ (S.admissible m) _ _ (ContinuousMap.continuous x) -- order
lemma strokeP (he:Action.flavor u X=Y)(hi:i≤N):Action.flavor u (TX i X)=TX i Y:=by refine moving A _ _ (fun _=> Action.flavor u) (fun m x=>?_) he hi; unfold Run.block; rw [step_brute,step_brute]; exact flavor_shift (stitch S r m) _ (S.admissible m) _ _ (ContinuousMap.continuous x) _
lemma checkered (he:Action.parity X=Y)(hi:i≤N):Action.parity (TX i X)=TX i Y:=by refine moving A _ _ (fun _=> Action.parity) (fun m x=>?_) he hi; unfold Run.block; rw [step_brute,step_brute]; exact (TorusPCAC.Finite.block_grade (stitch S r m) (S.admissible m) _ (ContinuousMap.continuous _) _ _).symm
lemma first (m:ℕ)(he:m ≤N)(b:Cover):march b (TX m Sn)=TX m Sn:= journey A Sn Sn b he (move_pivot _ _ rfl)
lemma arrives (m:ℕ)(he:m ≤N): (∀ (p:EuPin)(s:Signed), p.Lifts s→ Action.pin p s (TX m Sn)=TX m Sn) ∧ (∀ a:Axis,Action.adj a (TX m Sn)= TX m Sn)∧ (∀ u:FlavorTorus,Action.flavor u (TX m Sn)=TX m Sn) ∧ Action.charge (TX m Sn)=TX m Sn∧ Action.parity (TX m Sn)=TX m Sn:=by
    refine ⟨fun p s h=>pin_moves A s p Sn Sn h (Exposure.pin_pivot s p _ h rfl) he,fun a=>eyes A a Sn Sn (eye_pivot _ _ rfl) he,fun u=>strokeP A u Sn Sn (flavor_pivot ..) he, chargery A Sn Sn (charge_pivot ..) he, checkered A Sn Sn (funext ?_) he⟩
    intro x; unfold Action.parity; simp only [Regulator.density_apply,map_smul]; apply congr_arg; exact gauss_plus _
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.arrives

import YM.Lyre.Ascent
import YM.Lyre.Absolute
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open Transfer QCD.Cove
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
variable {S:Scheme}{R:Side}{N F i j:ℕ}(A:Run S N R F)
local notation "gR"=> S.side R
local notation "Pv" k=> S.step k
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola Plum Finset NormedSpace
variable (hA:A.Actual)
include hA
-- continuity & conservation
lemma armada (m:ℕ) (hi:m≤N): A.density m=⇑(S.toStop R A.β A.w N m A.regulator.density):=by
   induction hi using Nat.decreasingInduction with|self=> rw[Scheme.entrance]; exact hA.start|of_succ m hm ih=> rw [Scheme.next S R A.β A.w hm, hA.travels.eqn (Nat.zero_le _) hm, ih]; rfl
lemma scriptures (hi:i≤N):Continuous (A.density i):=by rw[armada A hA i hi]; exact ContinuousMap.continuous _
noncomputable def sig (i:ℕ)(z:Stud (gR i) F):ℂ:=joint z/ joint (A.density i)
lemma sig_smul (m:ℕ)(z:Stud (gR m) F)(t:ℂ): sig A m (t • z)= t*sig A m z:=by unfold sig; rw [stampB,mul_div_assoc]
lemma joint_sum {c:Side}(x y:Stud c F)(hx:Stays x)(hy:Stays y):joint (x+y)=joint x+joint y:=by
    unfold joint; simp_rw [Pi.add_apply,map_add]; exact integral_add ((hx.flows ((ber (Modes c F)).continuous_of_finiteDimensional)).intg _) ((hy.flows (ber (Modes c F)).continuous_of_finiteDimensional).intg _) -- signature auto hA
lemma sig_sum (m:ℕ)(x y:Stud (gR m) F)(hx:Stays x)(hy:Stays y): sig A m (x+y)=sig A m x+sig A m y:=by unfold sig; rw[joint_sum A hA _ _ hx hy,add_div]
lemma escalated (y:Stud (gR (i+1)) F)(hm:i<N)(hy:Stays y): sig A i (A.block i y)= sig A (i+1) y:=by
     unfold sig; rw[hA.travels.eqn (Nat.zero_le _) hm]; simp only [Run.block]; let M:= S.step i; let g:=growth (gR i) F (A.w i); have ht : g≠0:= pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hA.w_pos hm).ne'); rw [Transfer.conserves _ _ _ _ _ (S.admissible i) y ((reimburse _ _ y hy).intg _), Transfer.conserves _ _ _ _ _ (S.admissible _) _ (hA.travels.atStep (Nat.zero_le _) hm)]; exact mul_div_mul_left _ _ ht
lemma escal (y:Insertion (gR i) F)(hm:j ≤ i)(hy:i≤N): sig A j (⇑(S.toStop R A.β A.w i j y))= sig A i ⇑y:=by
    induction hm using Nat.decreasingInduction with | self=> rw[Scheme.entrance]; rfl| of_succ j hj ih=> rw[Scheme.next S R A.β A.w hj]; exact (escalated A hA (⇑(S.toStop R A.β A.w i (j+1) y)) (hj.trans_le hy) (stays (ContinuousMap.continuous _))).trans ih
lemma soaringL (x:Stud (gR i) F)(hi:i≤N)(hx:Stays x): sig A i (x * A.density i)=sig A N (climbH A i N x * A.density N):=by
     rw [hA.start, armada A hA i hi]; unfold sig; let t:= S.multiplier R A.w i N F; have ht0:t≠0:=by apply Finset.prod_ne_zero_iff.mpr; intro i h; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hA.w_pos (mem_Ico.mp h).2).ne')
     rw [soarL A _ hx hi _ (fun i hi hy=>(hA.w_pos hy).ne'), Scheme.conservation S R A.density _ hA.travels hi (Nat.zero_le _)]; rw [hA.start]; exact mul_div_mul_left _ _ ht0
lemma even_comm (x:Stud (gR i) F)(hi:i≤N): A.density i * x=x * A.density i:=funext fun V=>(hA.even hi V|>.central (x V)).symm.eq
omit hA
-- Literacy 
noncomputable def Accord (i j:ℕ) (X:ℂ) (Y:ℂ):= {z : Stud (gR i) F × Stud (gR j) F| Stays z.1 ∧ Stays z.2 ∧ X*sig A i z.1=Y* sig A j z.2}
include hA
lemma pricedL (i j:ℕ)(X Y:ℂ): ∃ P: Submodule ℂ ((Grid (gR i)→ Alg (Keys (gR i) F)) × (Grid (gR j)→ Alg (Keys (gR j) F))), (P:Set _)=Accord A i j X Y:=by
    refine ⟨{ carrier:= Accord A i j X Y
              add_mem':=fun {x y} h he=>?_
              zero_mem':=?_
              smul_mem':=fun z {x} h=>?_},rfl⟩ -- syntax columns hA issue
    · obtain ⟨h₁,h₂,H⟩:= (h:(Stays x.1 ∧ Stays x.2 ∧ X*_=_)); obtain ⟨h₃,h₄,hP⟩:=(he:(Stays y.1∧Stays y.2 ∧ X*_=_)); refine ⟨(h₁.both h₃).flows continuous_add,(h₂.both h₄).flows continuous_add,?_⟩; rw [Prod.fst_add, Prod.snd_add,sig_sum A hA i _ _ h₁ h₃,sig_sum A hA j _ _ h₂ h₄, mul_add,mul_add,H,hP]
    · refine ⟨stays continuous_const,stays continuous_const,?_⟩; simp [sig,joint]
    obtain ⟨h₁,h₂,H⟩:=(h:(Stays x.1 ∧ Stays x.2 ∧ X*_=_)); refine ⟨stockC _ _ h₁,stockC _ _ h₂,?_⟩; rw [Prod.smul_fst,Prod.smul_snd,sig_smul _ hA ,sig_smul _ hA ]; rw [mul_left_comm X, H,mul_left_comm]
section
open FlareV
variable {I:Type}[Fintype I](Q:I→Bool)(v:Finset I)(t:ℂ) (Y:I→ Stud (S.side R i) F)
-- Pulse data already equal relative to A via §Tera scaling.S.Product with q required homogeneous.
variable (E:Grid (S.side R j)→Patio (Keys (S.side R j) F⊕Spine I))
variable (f: ∀ k,Set (Site (S.side R k)))
-- marked startup budget.Mag moments.Bond statement: `t:Tera'`.*Reel.E all configs.This may not be zero.Ht.
variable (r:I→ℝ)(hp:∀ a:I,∀ V,Hom (Q a) (Y a V))(hS:∀ a:I,Stays (Y a))(U: I→ (k:ℕ)→ Set (Site (S.side R k)))(hv:∀ a∈v,Lease i N (U a))(hg:∀ a∈v,Uses (U a i) (Y a))(he:∀ a:I,Neutral (Y a)) (hd:∀ k:ℕ,i≤k→ k<N → ∀ a∈v,∀ b∈v,a≠b→Disjoint (U a k) (U b k))
variable (hi:i≤N)(hn:j ≤ i)
variable (hz:∀ (k:ℕ)(s:Fin k→I),Injective s→Quills.crest s ⊆ v→ let Z:= (numbered Q (Keys (S.side R j) F) s ∘ E) ; Stays Z ∧ t*sig A j Z = give r (Quills.crest s) *sig A i (A.density i * (List.ofFn fun a=> Y (s a)).prod))
-- unweighted launch gardens at bare pulls for each a; valid any activated tiling.A. Does not require Continuity after. Define corrected exact carrier. Momentum.Z ports.Matches.
include hp hi
noncomputable def radiant (V:Grid (S.side R N))(p:I):= emitK Q p (climbH A i N (Y p) V) (steep A _ _ (hS p) (hp p) hi V)
noncomputable def epochN (V: Grid (S.side R N)): Patio (Keys (S.side R N) F ⊕ Spine I):= rootR (Spine I) _ ⟨A.density N V,hA.even le_rfl V⟩* NormedSpace.exp (∑ p:I,radiant A Q Y hp hS hi V p) -- inspect args
lemma epicN {k:ℕ}(s:Fin k→I)(hs:Injective s) : numbered Q (Keys (S.side R N) F) s ∘ epochN A hA Q Y hp hS hi= A.density N * (List.ofFn fun a=>climbH A i N (Y (s a))).prod:=by
      funext V; rw [Function.comp_apply,epochN,needleE (Keys (S.side R N) F) Q s _ (fun a:I=> climbH A i N (Y a) V) _ (fun i=>rfl) hs,songX (gR N) (fun a=> climbH A i N (Y a)) s]; rfl
include hg he hv hS hd hz
lemma epitome {k:ℕ}(s:Fin k→I)(hs:Injective s)(ht:crest s⊆ v):
    let Y':= capstone (Keys (S.side R N) F) r ∘ epochN A hA Q Y hp hS hi; ((numbered Q _ s∘ E),(numbered Q _ s ∘ Y'))∈ Accord A j N t 1:=by
    intro Y'; obtain ⟨hc,hT⟩:=hz k s hs ht; let K:=Keys (gR N) F; let Z':= (numbered Q K s ∘ Y'); let X0:= (List.ofFn fun i=>Y (s i)).prod; let g:=give r (crest s); let Y₁(p:I):= climbH A i N (Y p); let Z:= (List.ofFn (fun a=> Y₁ (s a))).prod
    have heq: Z'=g • (A.density N * Z):=by
          rw [← (show numbered Q K s∘ epochN A hA Q Y hp hS hi= _ from epicN A hA Q Y hp hS hi s hs)]; exact funext fun X=> scale_read .. -- signature check
    have hSS:= flockZ Y₁ s (fun i _=>climbs A _ (hS i) hi); have hm:Stays Z':=heq.symm ▸ (stockC _ _ ((stays (scriptures A hA le_rfl)).mult hSS)) -- scriptures expects i implicit check
    refine ⟨hc,hm,?_⟩; rw [one_mul]; change t*_ = sig A N Z'; rw [hT,heq,sig_smul A hA,even_comm A hA _ hi,soaringL A hA X0 hi (flockZ Y _ (fun i hi=>hS i)), even_comm A hA _ (le_refl N)]
    congr 3 -- `climbH = List ...`
    let L:= List.ofFn s; have hx(p:I)(hx:p∈L):p∈v:=by obtain ⟨k,rfl⟩:= List.mem_ofFn.mp hx; exact ht ((exists_fix ..).2 ⟨k,rfl⟩)
    have hp:=pieces A L U Y (fun i hi=>⟨hS i,hg i (hx i hi),he i⟩) (fun i hi=> hv i (hx i hi)) (List.nodup_ofFn_ofInjective hs) (fun k hi he i hp j hh h=> hd k hi he i (hx i hp) j (hx j hh) h) hi; unfold L at hp; rw[List.map_ofFn,List.map_ofFn] at hp; exact hp
end
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.epitome
#print axioms YM.Massive.Lyre.pricedL

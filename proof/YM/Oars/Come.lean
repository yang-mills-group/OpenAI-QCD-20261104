import YM.Oars.Tin
import YM.VMarker.Totes
/-! # Renderer motion on same flags; no data tier chosen again inside hierarchy.V: -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {A B C I J E :Type}[Fintype A][Fintype B][Fintype C][Fintype I][Fintype J]
variable (A) (q:I→Bool)(p:J→Bool)(f:I→Option J)(g:I→J→ℝ)
local notation "R"=>Spine I
local notation "S"=>Spine J
local notation "Z"=> A⊕R
variable (r:I→J→Prop) {P:Set (Finset J)} {D:Set (Finset I)}(hp:Pledge q p r P D) {c:Side}{N:ℕ} {a b w:ℝ}(x:I→Site c)(y:J→Site c) (θ:ℝ)
-- preservation of unary arc. All-color, pin.Carry, puncture invariance
include hp
local notation "M"=>Keys c N
local notation "T"=> Patio (M⊕R)
local notation "L" j=>leaves M q p (findV r j) g
local notation "F" j=>flame M q p (findV r j) g -- notation conflicts.f implicit
variable (N)
local notation "↑I"=>banknote N x θ
local notation "↑J"=>banknote N y θ
local notation "↓J"=> withdraw N y θ
local notation "↓I"=>withdraw N x θ
local notation "Γ" a=>loft r P a
variable (P₀:I→Support c) (Pt:BudgetPoint)
variable (Y:Patron.Rail c (ample N I) E)
local notation "K" j => tent (D:=D) N P₀ Y j
local notation "Yᴮ"=>castR (D:=D) (P:=P) q p g r N x y θ P₀ Y -- check binder order.N explicitly.$
variable (hY:Wage.Tip N x q Y Pt θ a w)(ht:0<θ)(hq:Gully N x q θ P₀ Y)(hz:∀ i,x i∈ P₀ i)(hv:∀ i j,r i j → y j ∈ P₀ i)
namespace Recolor
include ht hp hY hq hv hz
open ConnectedActivityE6 Pressure
omit hv hq
variable (Bv:ℕ)(v:ℝ) (hα:∀ i,(opts r i).card ≤ Bv)(hΓ:0 ≤ v)(hΨ:∀ i j,r i j→ |g i j| ≤ v)
include hα hΓ hΨ
local notation "Γv"=>Bv*v
-- x.B coarse, v covers arbitrary polynomial.
-- include empty in all
set_option maxHeartbeats 490000 in
lemma buttons {δ:ℝ} (hD:0 ≤ δ)(i:E)(V:Grid c) : ‖Loom.token c (ample N J) θ ((Yᴮ).warp i V)‖*Real.exp (-(2*δ)*coverNumber Pt.B (Y.addr i).place) ≤ (1+∑ j∈ Film.seats x D (Y.addr i), (Γv)^j.card*Real.exp (-(2*δ)*coverNumber Pt.B (Y.addr i).place))*‖Loom.token c (ample N I) θ (Y.warp i V)‖:=by
    let u:=K i; let H:= Real.exp (-(2*δ)*coverNumber Pt.B (Y.addr i).place); let s:= Film.seats x D (Y.addr i); let w:=Y.warp i V; let Y' := ‖Loom.token c (ample N I) θ w‖; have HH:0 ≤ H:=Real.exp_nonneg _
    have hk : u ⊆ insert ∅ s:=by
      intro j hj; by_cases h:j=∅; · exact mem_insert.mpr (Or.inl h)
      obtain ⟨hP,Hj⟩:= (mem_filter.mp hj).2; apply mem_insert_of_mem; refine mem_filter.mpr ⟨mem_univ _,hP,Finset.nonempty_iff_ne_empty.mpr h,?_⟩; intro b hb; obtain ⟨k,hK,rfl⟩:=mem_image.mp hb; exact (mem_filter.mp (Hj hK)).2 (hz _)
    have hs : ∅∉ s:=fun h=>Finset.not_nonempty_empty ((mem_filter.mp h).2.2.1)
    have hZ(j:Finset I)(hj:j∈u): ‖Loom.token c (ample N J) θ (tinct (P:=P) q p g r N y θ j (↓I w))‖ ≤ (Γv)^j.card*Y':=by
        unfold tinct; rw [map_sum]; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i hi=> weightB q p g r hp N x y θ Pt Y hY ht _ V j i ((mem_filter.mp hi).2))).trans; rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (duties g r hp.mast _ hα j (fun i _=>hΨ i) hΓ) (norm_nonneg _)
    have hb: ‖Loom.token c (ample N J) θ ((Yᴮ).warp i V)‖ ≤ (∑ j∈u,(Γv)^j.card)*Y':=by
        change ‖Loom.token c (ample N J) θ (∑ j∈u, _)‖ ≤ _; rw [map_sum, Finset.sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum hZ)
    apply (mul_le_mul_of_nonneg_right hb HH).trans; rw [mul_right_comm,Finset.sum_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); refine (sum_le_sum_of_subset_of_nonneg hk (fun i _ _ => mul_nonneg (by positivity) HH)).trans ?_
    rw [sum_insert hs,Finset.card_empty,pow_zero,one_mul]; refine add_le_add_left ?_ _; unfold H; rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
include hv hq
set_option maxHeartbeats 660000 in
lemma scores {A δ τ:ℝ} (hA:a=A+2*δ)(hd:0<δ)(ht₀:0<τ)(hu:τ≤w) (h:∀ j:E,(1+∑ k∈Film.seats x D (Y.addr j),(Bv*v)^k.card *Real.exp (-(2*δ)*coverNumber Pt.B (Y.addr j).place))*τ ≤ w) : Wage.Tip N y p (Yᴮ) Pt θ A τ:=by
   obtain ⟨he,h1,h2⟩:= building q p g r hp N x y θ P₀ Pt Y hY ht hq hv; refine ⟨⟨he,h1,?_⟩,h2⟩
   let f (i:E):=1+∑ k∈Film.seats x D (Y.addr i),(Bv*v)^k.card *Real.exp (-(2*δ)*coverNumber Pt.B (Y.addr i).place); have hf i:0 ≤ f i:= add_nonneg (by norm_num) (sum_nonneg (fun j _=> by positivity)); let V i:= coverNumber Pt.B (Y.addr i).place; let g' i:= Real.exp (2*δ*V i)
   obtain ⟨f',hP,hL⟩:=hY.tilt.sold.cost; have hf'(i):0 ≤ f' i:= (norm_nonneg _).trans (hL i 1); refine ⟨fun i=> (f i*f' i)*g' i,?_,fun i U=>?_⟩
   · intro i; have h0:=ht₀.trans_le hu; refine budget_mono (hP i) (fun u=>?_) fun u=>?_
     · split; next h=> exact mul_nonneg (mul_nonneg (pow_nonneg ht₀.le _) (mul_nonneg (mul_nonneg (hf _) (hf' _)) (Real.exp_nonneg _))) (Real.exp_nonneg _)
       exact le_rfl
     split; swap; next hj=>rw [if_neg (show i∉Ruby.home Y u from hj)]
     next hj=>
       rw [if_pos (show i∈Ruby.home Y u from hj)]; let p:=(Y.addr u).inv.card; have he:0 < p:=Finset.card_pos.mpr (Y.addr u).alive; change τ^p*(f u*f' u*g' u)*Real.exp (A*_) ≤ w^p*f' u*Real.exp _
       have hv: τ^p*f u ≤ w^p:=by obtain ⟨k,hk⟩:= Nat.exists_eq_succ_of_ne_zero (show p ≠ 0 from Nat.ne_of_gt he); rw [hk,pow_succ,pow_succ,mul_assoc,mul_comm τ]; exact mul_le_mul (pow_le_pow_left₀ ht₀.le hu _) (h u) (mul_nonneg (hf _) ht₀.le) (pow_nonneg h0.le _)
       change _*Real.exp (A*V u) ≤ _*Real.exp (a*V u); rw [hA,add_mul A,Real.exp_add]; calc
          _= (τ^p*f u)*f' u*(Real.exp (A*V u)*g' u):=by ring
          _≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv (hf' _)) (by exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
   apply (div_le_iff₀ (Real.exp_pos (2*δ*V i))).1; rw [div_eq_mul_inv,← Real.exp_neg,←neg_mul]; exact (buttons q p g r hp N x y θ P₀ Pt Y hY ht hz Bv v hα hΓ hΨ hd.le i U).trans (mul_le_mul_of_nonneg_left (hL i U) (hf i)) -- div denominator v.Ri.M nx shape
end Recolor
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Recolor.scores

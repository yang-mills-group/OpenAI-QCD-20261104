import YM.Massive.PCAC.Redeem
/-!
# The passenger identity at one step of the joint gauge-spin RG.

`prepare_passenger`: linear coefficient bias, TWO laps explicitly carried (one
present after one transfer of any starting variation of this kind).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
open Finset
-- pointwise CLM actions on insertions. no assumption of neutral/even.
noncomputable def stroll (T:Fields c F→ₗ[ℂ]Fields c F): Insertion c F→ₗ[ℂ]Insertion c F where
    toFun x:= ⟨T∘x,T.continuous_of_finiteDimensional.comp x.continuous⟩
    map_add' x y:= ContinuousMap.ext fun i=> map_add T _ _
    map_smul' z x:= ContinuousMap.ext fun i=> by change T (z • x i)=z • T (x i); exact map_smul T z _
@[simp] lemma stroll_at (T:Fields c F→ₗ[ℂ]Fields c F)(x:Insertion c F)(U:Grid c): stroll T x U=T (x U):=rfl
noncomputable abbrev mark (k:Bool)(T:Sour (Modes c F)):= stroll (applyMark k T)
noncomputable abbrev arc (i j:Modes c F):= stroll (pairD i j)
abbrev Deck (c:Side)(F:ℕ):= Matrix (Modes c F) (Modes c F) (Insertion c F)
/-- `passenger`: full site-spin-flavor matrix. Man takes same order T(a,b)
with dpsi_a dbar_b. -/
def passenger (M:Deck c F): Insertion c F:= ∑ i:Modes c F,∑ j:Modes c F, arc i j (M i j)
lemma pax_apply (M:Deck c F)(U:Grid c): passenger M U=∑ i:Modes c F, ∑ j:Modes c F, pairD i j (M i j U):=by simp [passenger,arc]
@[simp] lemma pax_zero : passenger (0:Deck c F)=0:= by simp [passenger]
lemma pax_plus (M T:Deck c F): passenger (M+T)= passenger M+passenger T:=by simp [passenger,sum_add_distrib]
lemma pax_scale (M:Deck c F)(z:ℂ): passenger (z • M)=z • passenger M:=by simp [passenger,smul_sum]
noncomputable def bore (W:Sour (Modes c F))(X:Insertion c F): Deck c F:= Matrix.of fun i j=> W i j • X
lemma bore_at (W:Sour (Modes c F))(X:Insertion c F): passenger (bore W X)= stroll (lap W) X:=by ext1 U; rw [pax_apply,stroll_at,lap_apply]; apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _; exact map_smul (pairD u v) (W u v) (X U)

local notation "A"=> Modes f F -- A already var; maybe ambiguity
local notation "B"=> Modes c F
local notation "Q"=> qmove P h F
local notation "send"=> Transfer.blockMap P K h β w hk
noncomputable def berth (a b:A)(i j:B)(X:Insertion f F): Insertion f F:= ⟨fun U=> (Q U i a * ((Q U)ᴴ) b j) • X U, by have hx:=X.continuous; have hQ:=q_cont P h F; fun_prop⟩
noncomputable def Quilt (T:Deck f F): Deck c F:= fun i j=> send (∑ p:A×A, berth P h p.1 p.2 i j (T p.1 p.2)) -- Matrix.of?
variable (hw:0<w)
local notation "r"=> (w:ℂ)⁻¹^2
include hw
lemma berth_at (X:Insertion f F)(i j:A)(V:Grid f): steer P h w F V (arc i j X V)= ∑ p:B×B, r • pairD p.1 p.2 (steer P h w F V (berth P h i j p.1 p.2 X V)):=by
    have hp(a b:B): berth P h i j a b X V=(Q V a i * ((Q V)ᴴ) j b) • X V:=rfl
    rw [Fintype.sum_prod_type]; simp_rw [hp, v_smul, map_smul]; unfold steer; rw [show (arc i j X V)= _ from stroll_at (pairD i j) X V,pair_pass]; simp_rw [map_sum,map_smul, unpair w hw]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=> smul_comm ..
lemma carries (X:Insertion f F)(i j:A) : send (arc i j X) = r • ∑ p:B×B, arc p.1 p.2 (send (berth P h i j p.1 p.2 X)):=by
    ext1 U; rw [smul_sum, ContinuousMap.sum_apply]; let f(p:B×B):=r • pairD p.1 p.2; exact point_transfer P K h β w hk univ f (arc i j X) _ (berth_at P h w hw X i j) U
lemma quilting (T:Deck f F): send (passenger T)=r • passenger (Quilt P K h β w hk T):=by
    let m (p:A×A)(q:B×B):= arc q.1 q.2 (send (berth P h p.1 p.2 q.1 q.2 (T p.1 p.2)))
    unfold passenger; rw [← Fintype.sum_prod_type' (f:=fun i j=> arc i j (T i j))] -- name variant
    simp_rw [map_sum,carries _ _ _ _ _ _ hw]; rw [← smul_sum]; apply congr_arg; change (∑ p,∑ q,m p q)= _; rw [sum_comm, Fintype.sum_prod_type]; unfold Quilt; simp_rw [map_sum]; rfl
variable (U:Sour (Modes f F))(V:Sour (Modes c F))(hU:U.trace=0)(hV:V.trace=0)(he:∀ X:Grid f, (qmove P h F X)*U=V* (qmove P h F X))(hp:∀ X:Grid f,U*((qmove P h F X))ᴴ=((qmove P h F X))ᴴ*V)
include hU hV he hp hw
lemma shore (b:Bool)(X:Insertion f F): send (mark b U X)= mark b V (send X)- r • passenger (bore V (send X)):=by
    rw [bore_at]; ext1 E; let T:= applyMark b V-r • lap V
    have hv(L:Grid f): steer P h w F L (mark b U X L)= T (steer P h w F L (X L)):=by
       unfold steer; change rescale _ (Kit.sheath 1 (Q L) (applyMark b U (X L))) = _; rw [lap_contact (Q L) (X L) V (he L) (hp L) hV hU b,map_sub,resetMark,unlap w hw] -- lap_contact is apply−lap no smul. remove
       rfl
    have H:= point_transfer P K h β w hk ({(():Unit)}:Finset Unit) (fun _=>T) (mark b U X) (fun _=>X) (fun U=> by rw [sum_singleton]; exact hv U) E; rw [sum_singleton] at H; exact H
omit hw hU hV he hp
noncomputable def toward (Y:Insertion c F)(M:Deck f F) : Deck c F := r • (bore V Y+Quilt P K h β w hk M)
include hw hU hV he hp
/-- $M\mapsto w^{-2}(V\cdot X'+\mathcal B(Q M Q^†)$). `V` contains
pseudoscalar/spin generator option. Thus matrix here includes all the spin
and flavor factor of the bias. `passenger = sum dψ·dbar`. -/
theorem incident (b:Bool)(X:Insertion f F)(M:Deck f F):
    send (mark b U X-passenger M)= mark b V (send X)- passenger (toward P K h β w hk V (send X) M):=by
    rw [map_sub, shore P K h β w hk hw U V hU hV he hp, quilting P K h β w hk hw]; unfold toward; rw [pax_scale,pax_plus,smul_add]; abel
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.incident

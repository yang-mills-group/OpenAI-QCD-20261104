import YM.QCD.Jets.Vault
/-!
# Value receipts for opening a genuine massive step, no Germ assumption

Also retains gain on **long** high and on long low statistics.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Sun
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w p ε α β t:ℝ}{l b r:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
-- Real-valued test; compare to threshold on native support. True even without root include. Later use complements for pure principal calculation.
def broad (r l:ℕ)(i:Tr f): Prop:= Sum.elim (fun s=>fossil r l ≤ (coverNumber l s :ℝ)) (fun _=>True) i
lemma inverse_broad (r mL b:ℕ)(W: Support f→Support c)(he:∀ x,W x⊆enlargement S mL b x)(hb:0<b)(hv:l≤2*b)(hh:η≤u)(hr:reserve η w (conversion S mL) ε):
 Ac.Hit W b (fun i=> if broad r l (Sum.inl i) then P.sumX i else 0) w (rem G.L mL b w (Real.exp (-(u-η)*fossil r l)*q) ε):=by
    let X (x:Site f) (s:Support f):= ∑ y:Site f,(if broad r l (Sum.inl s) then P.Y x y s else 0)
    have hg x s: 0 ≤ X x s:=sum_nonneg fun i _=> by split; exact (P.X0.crop ..).1; exact le_rfl
    have hQ : (fun i:Support f=> if broad r l (Sum.inl i) then P.sumX i else 0)=fun i=> ∑ x,X x i:=by ext s; by_cases h:broad r l (Sum.inl s)<;>simp [X,sumX,h]
    rw [hQ]; refine body_hits S mL b l X W he hg (fun x s h=> ?_) hr hb hv _ ?_
    · contrapose! h; exact sum_eq_zero fun i _=> by split; exact (by_contra (fun he=> h (((P.X0.crop x i s).2.1 he).1))); exact rfl
    intro x; unfold X; simp_rw [mul_sum]; rw [sum_comm]; let E:=Real.exp (-(u-η)*fossil r l)
    calc
     _ ≤ ∑ j:Site f,E*duel P.Y x j u l:=by
       refine sum_le_sum fun i _=> ?_; unfold duel; rw [mul_sum]; apply sum_le_sum; intro s _; have hv:= (P.X0.crop x i s).1
       split
       next hl=>
         change fossil r l ≤ _ at hl; unfold Run.rent E; rw [← mul_assoc,← Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith only [mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hh)])) hv
       rw [mul_zero]; apply mul_nonneg (Real.exp_pos _).le; apply mul_nonneg (Real.exp_pos _).le hv
     _ ≤ _:=by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (P.X0.spends x) (Real.exp_pos _).le
-- augmented norm, not claiming ANYTHING beyond root for now
open Touch
lemma add_receipt {ι:Type*}(Y:ι→Support c)(Z₁ Z₂:ι→ℝ)(h₁:Ac.Hit Y b Z₁ a u)(h₂:Ac.Hit Y b Z₂ a v): Ac.Hit Y b (fun i=>Z₁ i + Z₂ i) a (u+v):=by
   intro i; convert! budget_plus (h₁ i) (h₂ i) using 1; funext j; split <;> simp [*]; ring

def terraceFee (F r mL b l :ℕ)(L:Side)(q u η w ε H x y:ℝ):= Real.exp 1* (fingers F^2*x⁻¹^2 * (rem L mL b w q ε + H* rem L mL b w (Real.exp (-(u-η)*fossil r l)*q) ε)+ H*(fingers F^2*(y*x⁻¹))*rem L mL b w (Real.exp (-(u-η)*fossil r l)*2*q) ε)
def tenderP (F r:ℕ)(x y H:ℝ): Tr f→ℝ :=fun i=> Real.exp 1*terra P F r x y i * (if broad r l i then H else 1)
lemma paysV (F r mL b:ℕ)(W: Tr f→Support c) (H:ℝ)(ht:1≤H)(he:∀ i,W i⊆enlargement S mL b (roomK i))(hx:0<x)(hy:0<y)(hb:0<b)(hv:l≤2*b)(hh:η≤u)(hd:reserve η w (conversion S mL) ε): Ac.Hit W b (tenderP P F r x y H) w (terraceFee F r mL b l G.L q u η w ε H x y):=by
   let Y i:=W (.inl i); let V i:= W (.inr i)
   let h₁:=fingers F^2*x⁻¹^2; let h₂:=fingers F^2*(y*x⁻¹)
   have hz: reserve u w (conversion S mL) ε:= ⟨hd.1,hd.2.1,hd.2.2.trans hh⟩
   have hX:= inverse_hits P r mL b Y (fun i=> he (.inl i)) hb hv hz; have hQ:= inverse_broad P r mL b Y (fun i=>he (.inl i)) hb hv hh hd
   have hW:= long_hits P r mL b V (fun i=> he (.inr i)) hb hv hh hd
   let z i:= terra P F r x y i*(if broad r l i then H else 1)
   have hp:Ac.Hit Y b (fun i=>z (.inl i)) w (h₁*(rem G.L mL b w q ε + H* rem G.L mL b w (Real.exp (-(u-η)*fossil r l)*q) ε)):=by
       let Z(i:Support f):= if broad r l (Sum.inl i) then P.sumX i else 0
       have h':0 ≤ H:=by linarith
       have hf:= add_receipt Y _ _ hX (heights_factor H Y Z (fun i=> H*Z i) hQ (fun _=>rfl) h')
       have ha:0≤h₁:= by unfold h₁; positivity
       have hm(i):0 ≤ P.sumX i:=sum_nonneg fun x _=>sum_nonneg fun j _=> (P.X0.crop ..).1
       have hg(i):terra P F r x y (.inl i)=h₁*P.sumX i:=by simp only [terra,Sum.elim_inl,h₁]; ring
       refine Labels.raise_prices _ _ (fun i=>by unfold z; rw [hg]; split<;>first | exact mul_nonneg (mul_nonneg ha (hm i)) zero_le_one|exact mul_nonneg (mul_nonneg ha (hm i)) h') (heights_factor h₁ _ _ (fun i=>h₁*(P.sumX i+H*Z i)) hf (fun _=>rfl) ha) fun i=>?_
       unfold z; rw [hg]; by_cases hi:broad r l (Sum.inl i)
       · rw [if_pos hi,show Z i=P.sumX i from if_pos hi, mul_assoc, mul_comm _ H]; gcongr; linarith [hm i]
       simp only [Z,hi,if_false,mul_one,mul_zero,add_zero,le_refl]
   have hL: Ac.Hit V b (fun i=> z (.inr i)) w (H*h₂ * rem G.L mL b w (Real.exp (-(u-η)*fossil r l)*2*q) ε):=heights_factor _ _ _ _ hW (fun i=>by
       unfold z; rw [if_pos (show broad r l (.inr i) from True.intro)]
       simp only [terra,Sum.elim_inr,h₂]; ring) (mul_nonneg (by linarith) (by unfold h₂; positivity))
   have hm:=Labels.together _ _ _ hp hL
   rw [show Sum.elim Y V= W from funext (fun i=>by cases i<;>rfl),show Sum.elim (fun i:Support f=>z (.inl i)) (fun i:Support f=>z (.inr i))=z from funext (fun i=>by cases i<;>rfl)] at hm
   exact heights_factor _ _ _ _ hm (fun i=>mul_assoc ..) (Real.exp_pos _).le
end YM.QCD.Jets.Sun
#print axioms YM.QCD.Jets.Sun.paysV

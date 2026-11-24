import YM.QCD.Spice.Zircon
import YM.QCD.Brick.Feather
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
section moment
open Brick Stew
variable {A D:Type*}[Fintype A][Fintype D]{p r q t d:ℝ}{g:D→ℕ}{f:A→ℕ}{U:Finset D}
variable (F G:Alg D →ₐ[ℂ] Alg A) (h:0<p)(hr:0 ≤r)
include h hr
lemma ropes (L: List D) (he:1 ≤ q) (hx:∀ i∈L,dryL p (F (atom i))≤r∧visc f p (F (atom i))≤q*r)(hQ:∀ i∈L,dryL p (G (atom i))≤r∧visc f p (G (atom i))≤q*r)(hD:∀ i∈L,dryL p (F (atom i)-G (atom i)) ≤ d*r ∧ visc f p (F (atom i)-G (atom i)) ≤ q*(d*r))(hd:0 ≤ d):
    let Y:=(L.map atom).prod; let X:= F Y-G Y
    dryL p X≤ d*(4*r)^L.length ∧ visc f p X ≤ q*d*(4*r)^L.length :=by
   have hv:0≤4*r:=by positivity
   have hz:0 ≤ q:=zero_le_one.trans he
   induction L with
   | nil=> intro Y X; rw [show X=0 from (by unfold X Y; simp),dryL,load_zero,visc,map_zero,norm_zero]; simp only [List.length_nil,pow_zero,mul_one]; exact ⟨hd,mul_nonneg hz hd⟩
   | cons i L ih=>
     intro Y X; let a:=atom i; let w:=(L.map atom).prod; let v:=(4*r)^L.length; let b:=(dryL p (F a))
     rw [show X=(F a-G a)*F w+ G a*(F w-G w) from (by unfold X Y; simp only [List.map_cons,List.prod_cons,map_mul]; unfold a w; rw [sub_mul,mul_sub]; abel),List.length_cons,pow_succ]
     have ht (P:D→Prop) (hp:∀ j∈i::L,P j):∀ j∈L,P j:= fun j hj=> hp j (List.mem_cons_of_mem _ hj)
     obtain ⟨h₀,h₁⟩:= ih (ht _ hx) (ht _ hQ) (ht _ hD); have hm:i∈ i::L:= List.mem_cons_self
     obtain ⟨h₂,h₃⟩:= hQ i hm; obtain ⟨h₄,h₅⟩:= hD i hm; obtain ⟨h₆,h₇⟩:= resist h he F L hr (ht _ hx)
     have hh: dryL p (F w)≤v:=h₆.trans (pow_le_pow_left₀ hr (by linarith) _); have hu:visc f p (F w)≤q*v:= h₇.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) hz)
     have hv': 0 ≤ v:= pow_nonneg hv _
     constructor
     · apply (spawnA ..).trans; apply (add_le_add ((load_mul ..).trans (mul_le_mul h₄ hh (load_nn ..) (mul_nonneg hd hr))) ((load_mul ..).trans (mul_le_mul h₂ h₀ (load_nn ..) hr))).trans; unfold v; nlinarith only [mul_nonneg (mul_nonneg hd hr) hv']
     apply (Brick.vested ..).trans; exact (add_le_add ((lightD h _ _).trans (add_le_add (mul_le_mul h₅ hh (load_nn ..) (by positivity)) (mul_le_mul h₄ hu (norm_nonneg _) (by positivity)))) ((lightD h _ _).trans (add_le_add (mul_le_mul h₃ h₀ (load_nn ..) (by positivity)) (mul_le_mul h₂ h₁ (norm_nonneg _) hr)))).trans_eq (by unfold v; ring)
lemma ropeP (S: Finset D) (he:∀ i∈S,dryL p (F (atom i)) ≤r∧ visc f p (F (atom i))≤(1+(g i:ℝ))^2*r) (hp:∀ i∈S,dryL p (G (atom i)) ≤r∧ visc f p (G (atom i))≤(1+(g i:ℝ))^2*r)
    (hD:∀ i∈S,dryL p (F (atom i)- G (atom i)) ≤ d*r ∧ visc f p (F (atom i)-G (atom i)) ≤ (1+(g i:ℝ))^2*(d*r))(hd:0≤d): visc f p (F (mono S)- G (mono S)) ≤ d*starch g (4*r) S:=by
     obtain ⟨L,hL,hs,hp'⟩:= expression S; let W:List D:=List.ofFn L; have ht i (hi : i∈W): i∈S:=by rw [hs]; simpa [W,Set.mem_range] using hi
     have hM:1 ≤ (pieD g S:ℝ):=Nat.one_le_cast.mpr (one_le_pow₀ (by omega))
     have hv i (h:i∈W):(1+(g i:ℝ))^2 ≤ (pieD g S:ℝ):=by unfold pieD; push_cast; gcongr; exact le_sup (ht _ h) (f:=g)
     rw [hp',show List.ofFn (atom ∘ L)= W.map atom by rw [List.map_ofFn]]; apply (ropes F G h hr W hM (fun i h=>⟨(he i (ht _ h)).1,(he i (ht _ h)).2.trans (mul_le_mul_of_nonneg_right (hv i h) hr)⟩) (fun i h=>⟨(hp i (ht _ h)).1,(hp i (ht _ h)).2.trans (mul_le_mul_of_nonneg_right (hv i h) hr)⟩) (fun i h=>⟨(hD i (ht _ h)).1,(hD i (ht _ h)).2.trans (mul_le_mul_of_nonneg_right (hv i h) (mul_nonneg hd hr))⟩) hd).2.trans_eq; rw [show W.length=S.card from List.length_ofFn,starch]; ring -- w shadows?
lemma rind (he:∀ i∈U,dryL p (F (atom i)) ≤r∧ visc f p (F (atom i))≤(1+(g i:ℝ))^2*r) (hp:∀ i∈U,dryL p (G (atom i)) ≤r∧ visc f p (G (atom i))≤(1+(g i:ℝ))^2*r)
    (hD:∀ i∈U,dryL p (F (atom i)- G (atom i)) ≤ d*r ∧ visc f p (F (atom i)-G (atom i)) ≤ (1+(g i:ℝ))^2*(d*r))(hd:0≤d) (x:Alg D)(hx:x∈region U): visc f p (F x- G x) ≤ d*visc g (4*r) x :=by
    conv_lhs=> rw [← write x,map_sum,map_sum,← sum_sub_distrib];
    apply (vc_sum ..).trans; rw [pricesD g (by linarith), Finset.mul_sum]; refine sum_le_sum fun i _=>?_ ; by_cases hi:i⊆U
    · rw [map_smul,map_smul,← smul_sub,vc_scale]; exact (mul_le_mul_of_nonneg_left (ropeP F G h hr i (fun j hj=> he _ (hi hj)) (fun j hj=> hp _ (hi hj)) (fun j hj=> hD j (hi hj)) hd) (norm_nonneg _)).trans_eq (by ring)
    rw [ember x hx i hi,norm_zero,mul_zero,mul_zero,zero_smul,map_zero,map_zero,sub_zero,visc,map_zero,norm_zero]
end moment
end YM.QCD.Spice

import YM.Lobo.Tyre
import YM.Lobo.Trident
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
noncomputable def ride(v:Bool) : List Axis:= if v then [0,1,2] else []
noncomputable def gait(f:Bool)(t:Bool): List Axis:= ride f ++ if t then [timeAxis] else []
abbrev GammaRow:=Option Tri × Bool × Bool
noncomputable def pearl (i:GammaRow): List Axis:= i.1.elim (gait i.2.1 i.2.2) (fun j=> lieu j :: gait i.2.1 i.2.2)
noncomputable def flat(i:GammaRow):Spike:=flair (pearl i)
-- trace pairing and sign via visa. distinct.
variable (a:Axis)(p q:GammaRow)
lemma shineEq (K:EuPin) (h:K.Lifts (Signed.mirror a)): conjug K (flat p)= visa (pearl p) (Signed.mirror a) • flat p:=by unfold flat; rw [flair_turn K _ h]; congr 1; rw [List.map_id'' _]; exact fun _=>rfl
-- use Boolean parity inequality by decide cheaply
private def cRide (i:GammaRow):List (Fin 4):= i.1.elim (if i.2.1 then [0,1,2]++ (if i.2.2 then [3] else []) else if i.2.2 then [3] else []) (fun j=> j.castSucc:: ((if i.2.1 then [0,1,2] else [])++ (if i.2.2 then [3] else [])))
private def marked (i:GammaRow)(j:Axis):Bool:=decide ((cRide i).count j%2=0)
set_option maxRecDepth 130000 in
set_option maxHeartbeats 2000000 in
private lemma differs : ∀ (w v:GammaRow),w≠v →∃ k: Fin 4,marked w k≠ marked v k:=by
      decide
lemma thrice : visa (pearl p) (Signed.mirror a) = if Lobo.marked p a then (1:ℂ) else -1:=by
     have he:cRide p=pearl p:=by rcases p with ⟨w,f,t⟩; cases w<;>cases f<;>cases t<;> rfl
     have hz(l:List Axis): visa l (Signed.mirror a)=if l.count a%2=0 then 1 else -1:=by
          induction l with
          | nil=> simp [visa]
          | cons b l ih=> rw [show visa _ _=(signT (Signed.mirror a) b:ℂ)* visa l _ from rfl,ih]; by_cases h:a=b
                          · subst b; rw [List.count_cons_self]; simp [signT,Signed.mirror]; split <;> split <;> first|rfl|norm_num|omega
                            all_goals omega
                          rw [List.count_cons_of_ne (Ne.symm h)]; simp [signT,Signed.mirror,h]
     simp only[marked,he,hz,decide_eq_true_eq]
private lemma sunLT (K:EuPin)(x:Spike): Matrix.trace (conjug K x)=Matrix.trace x:=by
      unfold conjug; rw [Matrix.trace_mul_comm,← mul_assoc,show K.matrix⁻¹.val*K.matrix.val=1 from K.matrix.inv_val, one_mul]
private lemma starL(K:EuPin)(x: Spike): conjug K (star x) = star (conjug K x):=by
     unfold conjug; rw [star_mul,star_mul,show star K.matrix⁻¹.val=K.matrix.val from ?_,show star K.matrix.val=K.matrix⁻¹.val from ?_,mul_assoc] -- E_star direction
     · exact (E_star _).symm
     rw [E_star,star_star]
lemma saltF (h:p ≠ q) : Matrix.trace (star (flat p)*flat q)=0:=by
     obtain ⟨k,hk⟩:=differs p q h; obtain ⟨G,hG⟩:=EuPin.choice (Signed.mirror k); let s:= Signed.mirror k; have he:=sunLT G (star (flat p)*flat q); rw [Oriole.L_up,starL,shineEq k p _ hG,shineEq k q _ hG,thrice,thrice] at he
     cases ha:marked p k <;> cases hb:marked q k <;> rw[ha,hb] at hk he <;> first|(exfalso; exact hk rfl)| (apply neg_eq_self.mp; simpa using he)
lemma saltN : Matrix.trace (star (flat p)*flat p)≠0:=by rw [show star (flat p)*flat p=1 from (flair_b _).1]; simp
noncomputable def lamp (p:GammaRow):Spike→ₗ[ℂ]ℂ:= Matrix.traceLinearMap Pinor ℂ ℂ ∘ₗ (LinearMap.mulLeft ℂ (star (flat p))) -- signature
lemma peaks : LinearIndependent ℂ flat:=by
     apply Fintype.linearIndependent_iff.mpr; intro g h k; have H:=congr_arg (lamp k) h; rw [_root_.map_sum,map_zero] at H; rw [sum_eq_single k] at H
     · rw [map_smul] at H; exact (mul_eq_zero.mp H).resolve_right (saltN k)
     · intro v _ h; rw [map_smul,show lamp k (flat v)=0 from saltF k v h.symm,smul_zero]
     simp
lemma indexF : Fintype.card GammaRow=Module.finrank ℂ Spike:=by rw [show Module.finrank ℂ Spike = _ from Module.finrank_matrix ℂ ℂ Pinor Pinor]; norm_num [GammaRow,Tri,Pinor] -- find syntax
lemma spans : Submodule.span ℂ (Set.range flat)=⊤:= by exact peaks.span_eq_top_of_card_eq_finrank' indexF
end YM.Lobo
#print axioms YM.Lobo.spans

import YM.QCD.Globe.Bromo
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Laurent Bloch QCD.Free Flume.Para Cost
variable (P:Plan j) {W s g t ν δ:ℝ}
lemma flipP {X:Sheet c}{w:Site c→Bundle}(hv:peel X=lined w)(h:∀ i, IsUnit (w i).det): IsUnit X.det ∧ X⁻¹=install (fun i=> (w i)⁻¹):=by
    let A:= install (fun i=> (w i)⁻¹); have hp : A*X=1:=by
       apply peel_injective; unfold A; rw [peel_mul,hv,Flume.carries,peel_one,lined_law, show ((fun i=>(w i)⁻¹) : Site c→Bundle)*w=(fun _=>1) from ?_]; exact ridden
       funext i; exact Matrix.nonsing_inv_mul _ (h i)
    exact ⟨Matrix.isUnit_det_of_left_inverse hp,Matrix.inv_eq_left_inv hp⟩
lemma stood (w:Site c→Bundle)(t:ℝ)(ht:0 ≤ t)(h:∀ i,‖w i‖ ≤t): ‖install w‖ ≤ t:=by
    have he: ‖leaf c‖≤1:= rotation_price (leaf_u c)
    have H: ‖lined w‖≤t:=by
        let d i j:= if i=j then ‖w i‖ else 0; refine wind_op ht _ d (fun i j=> ?_) (fun i=> by simpa [d] using h i) (fun i=>by simpa [d] using h i); rw [lined,Stew.board]; simp only [Equiv.refl_apply]; unfold d; split <;> simp
    apply le_trans (norm_mul_le (leaf c*lined w) _) ((mul_le_of_le_one_right (norm_nonneg _) (show ‖star (leaf c)‖≤1 by simpa using he)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) he).trans H))) -- order check
abbrev FawnP (P:Plan j)(C r T:ℝ): Prop:=∀ (v:Train j)(p:Momentum)(c:Side)(K:Sheet c)(m:ℝ), p∈baseCube→Beam K 6 r→ Drier K→ |m| ≤ T→ 0 < lengthSq p → let u:= Real.sqrt (C*lengthSq p+m^2);let H:= model (gleeM v p m)+pitchP K p; IsUnit H.det∧‖H⁻¹‖≤ (u/2)⁻¹
lemma throughX (hT:FawnP P ν s W)(A:ℝ)(hp:0 < A)(X:Sheet c)(v: Train j)(t:ℝ)(hB:Tempo X)(hf:Beam X 6 s)(h:Drier X)(he:|t| ≤ W)(hz:∀ p:Site c,A ≤ Real.sqrt (ν*lengthSq (tuning p)+t^2)):
   let D:=sunny P v c+(t:ℂ) • (1:Sheet c)+X; IsUnit D.det∧ ‖D⁻¹‖ ≤ (A/2)⁻¹:=by
    intro D
    let Z(p:Site c):= model (gleeM v (tuning p) t)+pitchP X (tuning p)
    have hv : peel D=lined Z:=by
        unfold D; rw [peel_add,peel_add,peel_smul,imageP hB, sunny,bare_this, unbarred,Flume.carries,peel_one,show (t:ℂ) • (1:Sheet c)=lined (fun _=> (t:ℂ) • (1:Bundle)) from ?_,lined,lined,lined,ride_add,ride_add]; congr 1; funext i; change rangeD v i+((t:ℂ) • 1)+_=Z i; unfold Z rangeD gleeM; rw [model_add,model_solo]; rfl
        nth_rw 1 [← ridden (X:=Site c)]; rw [ride_smul]; rfl -- issue
    have hm(p:Site c):IsUnit (Z p).det∧ ‖(Z p)⁻¹‖ ≤(A/2)⁻¹:=by
         obtain ⟨h1,h2⟩:=hT v (tuning p) c X t (keyboard p) hf h he (lengthSq_pos (tune_nonzero p)); exact ⟨h1,h2.trans (inv_anti₀ (half_pos hp) (div_le_div_of_nonneg_right (hz p) (by norm_num)))⟩
    obtain ⟨h1,h2⟩:= flipP hv (fun i=>(hm i).1); rw [h2]; exact ⟨h1,stood _ _ (by positivity) (fun i=>(hm i).2)⟩
-- uniform thick threshold
include P
lemma maxW (hT:FawnP P ν s W)(ht:0<ν)(M:ℕ)(B:Side)(hv:B.val=M)(d:ℝ)(hp:0<d):∃ C:ℝ,1≤ C ∧∀ c:Side, ∀ (X:Sheet c)(v:Train j)(t:ℝ), Tempo X→Beam X 6 s→ Drier X→ |t|≤W →(c=B∨ d ≤|t|)→ let Y:= sunny P v c+(t:ℂ) • (1:Sheet c)+X; IsUnit Y.det ∧ ‖Y⁻¹‖≤ C:=by
    have h(p:Site B):0 < Real.sqrt (ν*lengthSq (tuning p)):=by have he:=lengthSq_pos (tune_nonzero p); positivity
    let V:=univ (α:=Site B); let f:= fun p:Site B=> Real.sqrt (ν*lengthSq (tuning p)); obtain ⟨p,hp',hM⟩:= Finset.exists_min_image V f univ_nonempty
    let A:= min d (f p); have hA:0<A:= lt_min hp (h p); let H:= (A/2)⁻¹
    refine ⟨max 1 H,le_max_left ..,fun c X v t he hC hR hz hr=> ?_⟩; have hs(i:Site c): A ≤ _:= (show A ≤ Real.sqrt (ν*lengthSq (tuning i)+t^2) from ?_); swap
    · rcases hr with hr|hr
      · subst c; exact (min_le_right ..).trans ((hM i (mem_univ _)).trans (Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))))
      apply (min_le_left ..).trans (hr.trans _); apply le_trans _ (Real.sqrt_le_sqrt (le_add_of_nonneg_left (mul_nonneg ht.le (lengthSq_pos (tune_nonzero i)).le))); rw [Real.sqrt_sq_eq_abs]
    intro Y; obtain ⟨h1,h2⟩:= throughX _ hT _ hA X v t he hC hR hz hs; exact ⟨h1,h2.trans (le_max_right ..)⟩
end YM.QCD.Globe

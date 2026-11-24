import YM.QCD.Stew.Stocks
/-! # reading a single SU link and block matrices -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix 
variable {c:Side}{N n z:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset
variable {B: Support c}
-- bridge topologies via L linear map. Proof every `su.Mat` L2; rely compatibility of norm_top.
def colourLink (e:Edge (Site c)) (U:Grid c):Mat:= colour (U e)
section
open scoped Matrix.Norms.Frobenius
lemma scalar_bill (e:Edge (Site c))(U:Grid c)(q:ℕ)(i j:Hue): Chart q (fun V=> colourLink e V i j) U ∧∀ l:List (Directions su c), l.length≤q→ leftDerivs (fun V=> colourLink e V i j) l U=(YM.Work.G07.linkPrefix e l*su.mat (U e)) i j:=by
   let T:=LinearMap.toContinuousLinearMap ({ toFun:=fun M:su.Mat=> M i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}:su.Mat→ₗ[ℝ]ℂ) -- params
   have hF:Chart q (fun V:Grid c=>su.mat (V e)) U:=by
        unfold Chart; change ContDiffAt ℝ _ (fun x:Directions su c=> su.mat (su.lieExp (x e))*su.mat (U e)) _; exact ((su.exp_jet.of_le le_top).contDiffAt.comp 0 (contDiff_apply ..).contDiffAt).mul contDiffAt_const
   refine ⟨T.contDiff.contDiffAt.comp 0 hF,fun l hl=>?_⟩
   exact (Push.Local.left_linear T l hF hl).trans (congr_arg T (YM.Work.G07.left_link e l U))
end
open scoped Matrix.Norms.L2Operator
lemma link_chart (e:Edge (Site c)) (U:Grid c)(k:ℕ):Push.Local.Chart k (colourLink e) U:=by
   let P (x:Directions su c):=colourLink e (increment U x); let F (x:Directions su c) (i j:Hue):= P x i j; let L := LinearMap.toContinuousLinearMap ({ toFun:=fun f:Hue→Hue→ℂ=> Matrix.of f, map_add':=fun i j=>rfl,map_smul':=fun r x=>rfl } : (Hue→Hue→ℂ)→ₗ[ℝ] Mat)
   have he:ContDiffAt ℝ (k:ℕ∞ω) F 0:=by refine contDiffAt_pi.mpr fun i=>contDiffAt_pi.mpr fun j=>?_ ; exact (scalar_bill e U k i j).1
   exact L.contDiff.contDiffAt.comp 0 he
lemma leftC (e:Edge (Site c))(l:List (Directions su c))(U:Grid c): leftDerivs (colourLink e) l U= YM.Work.G07.linkPrefix e l*su.mat (U e):= by
    ext i j
    let T : Mat→L[ℝ] ℂ := LinearMap.toContinuousLinearMap ({ toFun:=fun x:Mat=> x i j, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl } : Mat→ₗ[ℝ]ℂ)
    exact (left_linear T l (link_chart e U l.length) le_rfl).symm.trans ((scalar_bill e U l.length i j).2 l le_rfl)
-- convert op tensor by measured Lipschitz. alternative derive full proof.
lemma leftU (M:Mat)(h:M ∈ unitary Mat): ‖M‖≤1:= Lat.rotation_price h
lemma amplitude :∃ C:ℝ,1≤C∧∀ A:su.Color,‖(show Mat from su.colorMat A)‖ ≤ C*‖A‖:=by
   let B:su.Color→ₗ[ℝ]Mat:={ toFun:=fun x=>su.colorMat x,map_add':=fun _ _=> map_add ..,map_smul':=fun r x=>map_smul (su.colorMat) ..}
   let X:= LinearMap.toContinuousLinearMap B
   exact ⟨max 1 ‖X‖, le_max_left ..,fun i=> (X.le_opNorm i).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))⟩
lemma prices (n b r:ℕ): ∃ C:ℝ,1≤C∧∀ (c:Side)(o:Site c)(e:Edge (Site c)),e.1∈ halo r {o} →∀ p: BudgetPoint,p.order ≤ n → p.power ≤ b→∀ l : List (Directions su c), l.length ≤p.order → (∀ x∈l,p.dirBound o x)→∀ U:Grid c, ‖leftDerivs (colourLink e) l U‖ ≤ C:=by
    obtain ⟨C,hC,h⟩:= amplitude; let X:= C*((1+r)^b); have hX:1 ≤ X:=one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by simp))
    refine ⟨X^n,one_le_pow₀ hX, fun c o e hp p hk hv l he hP U=> ?_⟩
    let g q:= YM.Work.G07.linkPrefix e (G:=su) q; have hh(s : List (Directions su c)) (hs: ∀ i∈s,p.dirBound o i) : ‖(show Mat from g s)‖ ≤ X^s.length:=by
       induction s with
       | nil=> change ‖(1:Mat)‖≤ X^0; rw [norm_one,pow_zero]
       | cons i s ih=>
          have hx:= hs i (by simp); let T:Mat:= g s; let D:Mat:= su.colorMat (i e)
          have hM : ‖D‖ ≤ X:=by
             apply (h _).trans; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC); apply (hx e).trans; apply (mul_le_of_le_one_left (by positivity [p.threshold_pos]) p.threshold_le).trans; change _≤(1+(r:ℝ))^b -- eta
             have hx : separation o e.1 ≤ r := by simpa only [halo_spec,Finset.mem_singleton,exists_eq_left] using hp
             refine (pow_le_pow_left₀ (by positivity) (by gcongr; exact_mod_cast ((separation_comm ..).trans_le hx)) _).trans (pow_le_pow_right₀ (by simp) hv)
          rw [List.length_cons,pow_succ]; apply le_trans _ (mul_le_mul (ih (fun i hi=> hs _ (by simp [hi]))) hM (norm_nonneg _) (pow_nonneg (zero_le_one.trans hX) _)); have hv : (show Mat from g (i::s))= T*D:= YM.Work.G07.linkPrefix_cons ..; rw [hv]; exact norm_mul_le ..
    let A: Mat:= g l; have hu : leftDerivs (colourLink e) l U= A * colourLink e U:= leftC ..; rw [hu]; apply (norm_mul_le ..).trans; rw [show X^n = X^n*1 from (mul_one _).symm]; exact mul_le_mul ((hh l hP).trans (pow_le_pow_right₀ hX (he.trans hk))) (leftU _ (U e).val.property) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hX) _)
end YM.QCD.Stew

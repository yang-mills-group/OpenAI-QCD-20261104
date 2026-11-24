import YM.Eden.Won
/-! # Small-field weight register. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek Next.Fluctuations
lemma plankS (q: Bool)(i:Dike)(p:Multi d)(n:Side)(x:Cover)(U : Grid n): rateS d x U (lineT q (place p i))=∑ w∈ (rider p).support, (↑(rider p w):ℂ) • beams q n x w U i:=by
    have hp:=congr_fun (congr_fun (whirly p i q) n) x; apply Eq.trans _ (Eq.trans (DFunLike.congr_fun hp U) ?_)
    · rw [wow,power_t,map_one,one_smul]
    rw[Finset.sum_apply, Finset.sum_apply,ContinuousMap.sum_apply]; rfl
lemma momentH (z:Sings d) : ∃ C:ℝ,0≤ C ∧∀ {n:Side}(x:Cover)(U:Grid n) (F:ℝ),0≤ F → nob su F U → ‖rateS d x (1:Grid n) (Grass.atom z)‖ ≤ C ∧ ‖rateS d x U (Grass.atom z)-rateS d x (1:Grid n) (Grass.atom z)‖≤ C*F:=by
    obtain ⟨q,p,i,hp⟩:=spots z; let Z:=rider p; let W:=Z.support; choose C hc H using (fun w: Walk=> role_fee w q i); let a:=∑ i∈W, ‖Z i‖; let b:=∑ i∈W,‖Z i‖*C i; have h:0≤ a:=sum_nonneg fun _ _=>norm_nonneg _; refine ⟨max a b,h.trans (le_max_left ..),fun {n} x U F ht hX=>?_⟩; rw [hp,plankS,plankS]; constructor
    · apply (norm_sum_le ..).trans; apply le_trans _ (show a ≤ max a b from le_max_left ..); apply sum_le_sum; intro i' _; rw [norm_smul,Complex.norm_real,beams_idle,norm_smul, Poised.Pipes.ap_one,one_mul, show ‖lineT q (place (landsE n x i') i)‖=1 from (by cases q; exact Grass.norm_atom ..; exact Grass.norm_atom ..),mul_one]
    rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right a b) ht); unfold b; rw [sum_mul]; refine sum_le_sum fun i' h=> ?_; rw [← smul_sub,norm_smul,Complex.norm_real, mul_assoc]; exact mul_le_mul_of_nonneg_left (H i' x U F hX) (norm_nonneg _)
-- ledger. Evo linear.E
noncomputable def taxG (d:ℕ)(x:Cover)(U:Grid n)(η:ℝ): Lily su d→ₐ[ℂ]ℂ:=nestK (η • uniR su U x)
noncomputable def taxP (d:ℕ)(x:Cover)(U:Grid n)(η:ℝ): Bard d →ₗ[ℂ]Lat.Fields n 6:= ((TensorProduct.lid ℂ _).toLinearMap).comp (TensorProduct.map (taxG d x U η).toLinearMap (rateS d x (1:Grid n)).toLinearMap)
lemma testimonP (X:Lily su d)(V:SpinPol d)(x:Cover)(U:Grid n)(η:ℝ): taxP d x U η (X⊗ₜ[ℂ]V) = taxG d x U η X • rateS d x (1:Grid n) V:=by unfold taxP; rw[LinearMap.comp_apply,TensorProduct.map_tmul]; rfl
section
variable {L:Type*}[NormedRing L]
structure Rover (X Y:L)(C M:ℝ):Prop where
   normP : ‖X‖ ≤ C
   buds : ‖Y-X‖≤ C*M
lemma Rover.raise {X Y:L}{C M S:ℝ} (h:Rover X Y C M)(hv:C≤ S)(ht:0≤ M): Rover X Y S M:=⟨h.normP.trans hv,h.buds.trans (mul_le_mul_of_nonneg_right hv ht)⟩
lemma Rover.bearing {X Y:L}{C M:ℝ}(h:Rover X Y C M)(hv: M≤1): ‖Y‖ ≤C+C:= (norm_le_norm_sub_add ..).trans (add_le_add (h.buds.trans (mul_le_of_le_one_right ((norm_nonneg _).trans h.normP) hv)) h.normP)
lemma Rover.and {X Y U V:L}{C D A:ℝ}(h:Rover X Y C A)(ht:Rover U V D A)(he:A ≤1) : Rover (X*U) (Y*V) (3*C*D) A:=by
    have hC:0 ≤ C:=(norm_nonneg _).trans h.normP; have hD:0≤ D:=(norm_nonneg _).trans ht.normP; refine ⟨(norm_mul_le X U).trans ((mul_le_mul h.normP ht.normP (norm_nonneg _) hC).trans (?_)),?_⟩; · nlinarith only [mul_nonneg hC hD]
    calc
      ‖Y*V-X*U‖ ≤ ‖Y*V-X*V‖+‖X*V-X*U‖:=norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ C*A*(D+D)+C*(D*A):=by rw [←sub_mul,← mul_sub]; exact add_le_add ((norm_mul_le ..).trans (mul_le_mul h.buds (ht.bearing he) (norm_nonneg _) ((norm_nonneg _).trans h.buds))) ((norm_mul_le ..).trans (mul_le_mul h.normP ht.buds (norm_nonneg _) hC))
      _=_:=by ring
end
section buds
local notation "r₀"=> Lχ
lemma Ppair (x:Tube su d) : ∃ C:ℝ,0≤C∧∀ {n:Side}(v:Cover) (U:Grid n)(η F:ℝ),0≤η→0≤ F→nob su F U→ Rover (taxP d v U η (Gχ x)) (powerG d v U η (Gχ x)) (C*(η*F)) F:=by
    obtain ⟨C,hc,h⟩:= ray_bound x; refine ⟨C,hc,fun {n} z U η F hη hf hF=>?_⟩; obtain ⟨h1,h2⟩:=h z U hF hf; unfold Gχ; rw [testimonP, power_t,map_one,map_one]; unfold taxG incomeF nestK; rw [MvPolynomial.aeval_X,MvPolynomial.aeval_X]; let P:=Bach su d (expandAt (wrap n z) U) x; let Q:=uniR su U z x; change Rover ((↑(η*Q):ℂ) • _) ((↑(η*P):ℂ) • _) _ _; constructor
    · rw [norm_smul, norm_one, mul_one,Complex.norm_real,norm_mul,Real.norm_of_nonneg hη]; exact (mul_le_mul_of_nonneg_left h1 hη).trans (le_of_eq (by ring))
    rw[←sub_smul,norm_smul,norm_one,mul_one,← Complex.ofReal_sub,Complex.norm_real,← mul_sub,norm_mul,Real.norm_of_nonneg hη]; exact (mul_le_mul_of_nonneg_left h2 hη).trans (le_of_eq (by ring))
lemma Epair (x:Sings d) : ∃ C:ℝ,0≤ C ∧∀ {n:Side}(v:Cover)(U:Grid n)(η F:ℝ),0 ≤ F→ nob su F U→ Rover (taxP d v U η (Gξ x)) (powerG d v U η (Gξ x)) C F:=by obtain ⟨C,hc,h⟩:=momentH x; refine ⟨C,hc,fun {n} v U η F hf hF=>?_⟩; unfold Gξ; rw [testimonP,power_t,map_one,map_one,one_smul,one_smul]; exact ⟨(h v U F hf hF).1,(h v U F hf hF).2⟩
lemma spinning {x y:Lily su d}{p q:SpinPol d}(v:Cover)(U:Grid n)(η F:ℝ) {C D:ℝ}(ht:F≤1)(h:Rover (taxP d v U η (x⊗ₜ[ℂ]p)) (powerG d v U η (x⊗ₜ[ℂ]p)) C F)(hp:Rover (taxP d v U η (y⊗ₜ[ℂ]q)) (powerG d v U η (y⊗ₜ[ℂ]q)) D F):
    let w:=(x⊗ₜ[ℂ]p)*(y⊗ₜ[ℂ]q); Rover (taxP d v U η w) (powerG d v U η w) (3*C*D) F:=by
    intro w; rw [← wow] at h hp -- each? remove
    rw [←wow]; unfold w; rw [weld,Pi.mul_apply,Pi.mul_apply,ContinuousMap.mul_apply]; have he:=h.and hp ht; rw [testimonP,testimonP] at he; rw[Algebra.TensorProduct.tmul_mul_tmul,testimonP,map_mul,map_mul]; simpa only [_root_.smul_mul_assoc, _root_.mul_smul_comm,smul_smul,mul_comm (taxG d v U η y)] using he
end buds
end YM.Eden
#print axioms YM.Eden.momentH
#print axioms YM.Eden.spinning

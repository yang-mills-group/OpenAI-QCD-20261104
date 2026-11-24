import YM.QCD.Globe.Scrip
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
variable {a b C δ:ℝ}{X Y:EvenA c N}
open Trees Nola
lemma worn (A:Sheet c)(hp:IsUnit A.det)(hv: fade (copies N A⁻¹) (exp X.val)=exp Y.val) : pebble (paleF N A+X) = ‖A.det^N‖* ‖Complex.exp (UPr Y)‖:=by
   let P:=copies N A; let Q: Matrix (Fin 0) (Modes c N) ℂ:=0; let F:=adapter (P⁻¹*Qᴴ) (Q*P⁻¹)ᵀ
   have he:IsUnit P.det:=by unfold P; rw [copies_det]; exact hp.pow _
   have hh: P+Qᴴ*Q=P:=by simp[Q]
   have hr: fade (P+Qᴴ*Q)⁻¹ (exp X.val)=exp Y.val:=by rw [hh]; exact (linked A N hp).symm ▸ hv
   have hz:= kinderR P Q X Y (by rw [hh]; exact he) hr; dsimp only at hz; rw [hh,← map_weight] at hz
   have ht (Z:Alg (Keys c N)): F Z=coef ∅ Z • 1:=by
      rw [← write Z]; simp only [map_sum,map_smul]; rw [sum_eq_single (∅:Finset (Keys c N))]
      · rw [mono_empty,map_one,sum_eq_single (∅:Finset (Keys c N))]; · simp only [map_smul, Grass.read,smul_eq_mul,mul_one]
        · intro j _ hj; rw [Grass.read_other _ _ hj.symm,smul_zero]
        simp
      · intro i _ hi; have hl : F (mono i) ∈ Grass.layer _ i.card:= exterior_layer _ (homogeneous i); rw [Grass.overflow hl ?_,smul_zero]; simp only [Pairs,Fintype.card_sum,Fintype.card_fin,zero_add]; exact Finset.card_pos.mpr (nonempty_iff_ne_empty.mpr hi)
      simp
   rw [show F (exp Y.val)=Complex.exp (UPr Y) • (1:Dirac (Fin 0)) from ?_] at hz; swap; -- branch order
   · rw [ht]; refine congr_arg (fun c:ℂ=> c • (1:Dirac (Fin 0))) ?_; change _= Complex.exp (mud Y); change _= _; rw [show Y.val = light _ Y from rfl,← Cove.light_exp]; exact Coda.term Y
   let R:=1-Q*P⁻¹*Qᴴ; have hq : ber _ (gauss R * (Complex.exp (UPr Y) • 1)) = Complex.exp (UPr Y):=by rw [Algebra.mul_smul_comm, mul_one,map_smul,det_amplitude,Matrix.det_isEmpty,smul_eq_mul,mul_one]
   unfold pebble; rw [oaks,← insulate (by norm_num : (1:ℝ)≠0) Q, hz,map_smul]; rw [hq,norm_smul, show P.det=A.det^N from copies_det ..]
lemma lighten (Z: EvenA c N)(hv:GrassA Z a m b)(hp:0<a):GrassA Z a 0 b:=by
    apply le_trans _ hv; refine sum_le_sum fun i _=>?_ ; unfold grainH Nola.tell; rw [pow_zero]; apply mul_le_mul_of_nonneg_left (one_le_pow₀ (by simp)) (by positivity)
lemma terminus (N:ℕ)(C:ℝ)(he:1≤ C) (δ:ℝ)(hδ:0<δ)(hx:δ ≤1)(hk:degreePriceCard (Real.exp δ-1) 1 ≤1/2) : ∀ᶠ t:ℝ in atTop, ∃ W:ℝ,0≤ W ∧∀ (c:Side)(K:Sheet c)(X:EvenA c N), Beam K⁻¹ 0 C→IsUnit K.det → Cocoa X → Pure X → GrassA X (2*(Real.exp 2*t)) 6 (δ/2) → expo W c ≤ pebble (paleF N K+X):=by
   let Y:= δ/2; let V:=Real.exp 4*((Fintype.card (Brick.Note N):ℝ)^2*(2*C)); let Z:= (Real.exp δ-1)*2
   obtain ⟨M,hM,H⟩:=heft (C:=V) (T:=Y) (by unfold V; positivity) (half_pos hδ)
   filter_upwards [eventually_ge_atTop M] with t ht; have h:0<t:=zero_lt_one.trans_le (hM.trans ht); have hz:0 ≤ Z:= by unfold Z; have hX:1 ≤ Real.exp δ:= Real.one_le_exp hδ.le; linarith
   let J:ℝ:= (Fintype.card Fiber:ℝ)*N*Real.log C -- verify casts
   have hJ:0 ≤ J:=by unfold J; positivity [Real.log_nonneg he]
   refine ⟨J+Z,add_nonneg hJ hz,fun c K X hp hi he' hq hP=>?_⟩; have ht:= H _ ht
   have hf : (1:ℝ)⁻¹*(δ/2)+t⁻¹^2*Real.exp 4*((Fintype.card (Brick.Note N):ℝ)^2*(2*C)) ≤ δ:=by unfold Y V at ht; rw [inv_one,one_mul]; linarith only [ht]
   obtain ⟨X',hv,hX⟩:= Nola.roiling (s:=Real.exp 2*t) (m:=0) locationP (copies N K⁻¹) X (fun i=>radiantB K⁻¹ hp i N) h zero_lt_one le_rfl rfl (GrassA.fetch X (lighten X hP (by positivity)) he' (by positivity)) hδ hx hk hf (hq ∅ (by simp))
   have hs: GrassA X' t 0 Z:=by
       apply hX.trans_eq; unfold Z; rw [one_mul,mul_assoc]
   rw [worn K hi hv, expo,mul_add,Real.exp_add]; apply mul_le_mul (detRatio K hi hp (zero_lt_one.trans_le he) N) _ (Real.exp_pos _).le (norm_nonneg _)
   rw [Complex.norm_exp]; apply Real.exp_monotone; have he := (abs_le.mp ((Complex.abs_re_le_norm _).trans (massB X' h hs))).1; linarith
end YM.QCD.Globe

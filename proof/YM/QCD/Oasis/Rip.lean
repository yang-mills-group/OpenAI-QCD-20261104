import YM.QCD.Oasis.Drizzle
/-!
# Provisions at real Grassmann norm. Banach estimate uniform even exp.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {P : Teller G} {c f : Side} {S : StepData c f} {p v d A B M U D W w q r b : ℝ} {F : Forest S.ratio} {N j n:ℕ}
local notation "R"=> Poll.Body (Precision.Key F G)
local notation "Xs"=> Positions (Uniform.Primary c G)
variable {ρ: Positions (Uniform.Primary c G) → Poll.Body (Precision.Key F G)} (T:F.Slice G→EvenA c N)
local notation "V" => (fun (x: Xs)=> represent (tint G _ x))
-- potential native all orientation
abbrev glimB (F':F.Slice G→ EvenA c N)(i:Xs × R): EvenA c N:= F' (draw F (V i.1) i.2)
noncomputable def heat (T':F.Slice G→ EvenA c N)(ρ: Xs → Poll.Body (Precision.Key F G))(i:Xs)(U:F.Slice G):EvenA c N:= exp (T' U -glimB T' (i,ρ i))-1
lemma remind (x:EvenA c N): ‖exp x‖ ≤ Real.exp ‖x‖:=by
   exact (sub_le_iff_le_add'.mp ((norm_sub_norm_le ..).trans (stipend _ (le_refl ‖x‖)))).trans_eq (by rw [norm_one]; ring) -- order exp
-- factor τ independent of i. local turns for corners.
abbrev strain (j:ℕ):ℝ:= letterP 1 j*Real.exp 1
lemma topex : Brush j (strain j) 1 (exp (𝔸:=EvenA c N)) (0:EvenA c N):=by
    apply beau zero_lt_one (fun i _=> (NormedSpace.exp_analytic (𝕂:=ℂ) (𝔸:=EvenA c N) _).differentiableAt); exact fun i hi=> (remind i).trans (Real.exp_monotone (mem_ball_zero_iff.mp hi).le)
local notation "τ"=> glimB T
lemma lapE (x: Xs)(h : Brush j M W (goreR (τ) ρ) x)(V': F.Slice G): let K:= exp (T V'-τ (x,ρ x)); let p':= clump j (M*(1+W)^j+M*(1+W)^j) (strain j)
     Brush j ((p'+1)*(‖K‖+1)) 1 (fun y=> heat T ρ y V') x :=by
      intro K p'; have he:= h.trim
      have hf:= (Brush.certified (k:=j) (x:=x) zero_le_one (goreR (τ) ρ x)).climb he.bound le_rfl
      let f i:=τ (x,ρ x) -τ (i,ρ i)
      have hh i : f i = goreR (τ) ρ x-goreR (τ) ρ i:= by unfold f goreR; abel
      have hs: Brush j p' 1 (fun i=>exp (f i)) x:=composite ((hf.separating he).shimmy (g:=f) (Eventually.of_forall hh)) (show Brush j _ 1 exp (f x) from by rw [hh,sub_self]; exact topex)
      have hk:= ((certified (k:=j) (x:=x) (le_refl 0) K).paints hs); rw [zero_add] at hk; refine ((hk.separating (certified zero_le_one (1:EvenA c N))).climb ?_ le_rfl).shimmy (Eventually.of_forall fun i=> ?_)
      · rw [norm_one]; nlinarith only [norm_nonneg K,hs.nonneg]
      change heat _ _ _ _= exp _ * exp _ - 1; rw [← NormedSpace.exp_add]; unfold heat; congr 2; unfold f; abel
abbrev roofT (j:ℕ)(U d:ℝ):=clump j (d*(1+U⁻¹)^j+d*(1+U⁻¹)^j) (strain j)+1
lemma crispX (h:∀ x,‖x‖<U→Brush (j+2) p 1 ρ x)(hu:0<U)(hs: U≤1)(hp:ρ 0=0)(hD:0≤D) (hL : TellerX (τ) (spanV D p) U v w (j+2)) (hC: Continuous T)(hq: U*growT (j+2) p D w v ≤1)(hF:∀ i, ‖T i‖ ≤ r)(hB:Real.exp (r+r)+2 ≤ W)(hv :0<gStep b)(hi:gStep b < U) (hP: roofT j U (keenR (j+2) p D v w U) ≤ A):
       Corn (heat T ρ) ρ D U W A (v*D) (dawnT (j+2) p D w v) (Real.exp 1+1) W j b:=by
   obtain ⟨X,hX,H⟩:=hL.lien
   let K :=nudge F (heat T ρ) ρ; have hc x:Continuous (fun y:R=> τ (x,y)):= hC.comp (draw_cont F (V x))
   have hJ: K = fun z x=> exp (lyric (τ) ρ z x)-1:=by
       funext z x; simp only [K,heat,lyric,hpoint,glimB,one_mul,one_smul,smul_zero,add_zero] -- edit
   constructor
   · obtain ⟨a,b,c,d,t,u,j⟩ := cotillon h hu hs hp (by omega) H hX hc hq
     rw [show nudge F (heat T ρ) ρ= _ from hJ]; exact ⟨_,a,b,c,d,t,u,j⟩
   intro x hx; let g V':= exp (T V'-τ (x,ρ x)); have hk: Continuous g:= exp_continuous.comp (hC.sub continuous_const)
   have ht j:‖T j-τ (x,ρ x)‖≤r+r:=(norm_sub_le ..).trans (add_le_add (hF j) (hF _)); have hh j : ‖g j‖ ≤ Real.exp (r+r):= (remind _).trans (Real.exp_monotone (ht _))
   have hz V':‖heat T ρ x V'‖≤ W:= ((norm_sub_le ..).trans (add_le_add (hh V') norm_one.le)).trans ((add_le_add le_rfl (by norm_num : (1:ℝ)≤2)).trans hB)
   let C i:= ‖g i‖+1; have hg i :0≤ C i:=add_nonneg (norm_nonneg _) zero_le_one; have hw i: |C i|≤ W:=by rw [abs_of_nonneg (hg i)]; exact (add_le_add (hh i) (by norm_num : (1:ℝ)≤2)).trans hB
   have hy :=(orbitsR h hu hs hp (by omega) H hX hD _ hx).smaller (show j≤j+2 from by omega)
   refine ⟨⟨(hk.sub continuous_const).measurable,_,hz⟩,hz,C,⟨(hk.norm.add continuous_const).measurable,W,hw⟩,fun i=>(lapE T x hy i).climb (mul_le_mul_of_nonneg_right hP (hg _)) le_rfl,hw,?_⟩
   rintro i ⟨z,⟨l,hl,rfl⟩,rfl⟩; rw [abs_of_nonneg (hg _)]
   let a:= ((gStep b),x); have hv' := toldR h hu hs hp (by omega) H hX (mem_closedBall_zero_iff.mp hl) (U⁻¹ • a) (show ‖U⁻¹ • a‖ < 1 from ?_)
   rotate_left
   · rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hu).le,mul_comm,← div_eq_mul_inv,div_lt_one hu]; apply max_lt (by rw [Real.norm_of_nonneg hv.le]; exact hi) hx
   have hp': ‖lyric (τ) ρ l a‖ ≤ 1:=by simpa only [smul_inv_smul₀ hu.ne'] using le_trans hv'.2.bound hq
   apply add_le_add _ le_rfl; unfold g; apply (remind _).trans; apply Real.exp_monotone; simpa only [a,lyric,glimB,hpoint,one_mul,one_smul,smul_zero,add_zero] using hp'
end YM.QCD.Oasis

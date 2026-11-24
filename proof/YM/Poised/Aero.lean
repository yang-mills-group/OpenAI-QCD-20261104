import YM.Poised.Floe
import YM.Planned.PRIMARY_INTEGRAL_295.Cases
/-!
# Joint chart on the torus, all actual roots
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {J B : Type}{d a l k n:ℕ}{c:Side}
namespace Pipes
open Beacon Gem MultiNext.SignedSource
variable (T:Taper) (b:Cover) [Fintype B] {V:Support c}
def frond (b:Cover)(x:Site c):ℂ:=ap c (offset b x+b)
variable (hx : Nonwrapping V (wrap c b)) (ht:100 ≤ c.val)
include hx ht
omit [Fintype B] in -- warning B unused
lemma house_p (x:Site c) (h:x∈V)(i:Axis)(s:ℝ)(hs:s∈Set.Ioo (-1:ℝ) 2) : T.χ ((c.val:ℝ)⁻¹ • (vector (offset b x)+s • basis i))=1:=by
   apply T.near; intro a; let P:=offset b x
   have hg : 10*(P a).natAbs<c.val:=Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 10 (component_le (x-wrap c b) a)) (hx _ h)
   have hv : |basis i a|≤1:=by by_cases i=a <;> simp [basis, *]
   change |(c.val:ℝ)⁻¹*((P a:ℝ)+s*basis i a)| ≤ _; have hQ:(100:ℝ) ≤ c.val:=by exact_mod_cast ht
   rw [abs_mul,abs_of_pos (by positivity)]; apply le_trans (b:= (c.val:ℝ)⁻¹ * ((P a).natAbs+2:ℝ))
   · apply mul_le_mul_of_nonneg_left _ (by positivity); refine (abs_add_le ..).trans (add_le_add ?_ ?_); · rw [Nat.cast_natAbs]; exact le_of_eq (by norm_cast)
     rw [abs_mul]; apply (mul_le_of_le_one_right (abs_nonneg _) hv).trans; rw [abs_le]; exact ⟨by linarith [hs.1],hs.2.le⟩
   rw [mul_comm,← div_eq_mul_inv, div_le_iff₀ (by positivity)]; have hg:(10:ℝ)*(P a).natAbs < c.val:= by exact_mod_cast hg
   linarith
lemma fronds (x:Site c)(h:x∈V): spun T b x= frond b x:=by
   have hh:=house_p T b hx ht x h timeAxis 0 (show _ from ⟨by norm_num,by norm_num⟩); rw [zero_smul,add_zero] at hh; simp only [spun,hh,Complex.ofReal_one,one_mul]; rfl
lemma lastX (i: Edge (Site c)) (hh:Mom.needed V i): offset b (i.1+Lattice.step i.2)=offset b i.1+Lattice.step i.2:=by
   unfold offset; apply Next.Foundations.lift_end (by omega) hx _ hh.1
variable (H:TaperHol) (A:Source.Hol su)
lemma traverse (W:Ln d)(i:Edge (Site c))(hi:Mom.needed V i) : views H b d W i=A.links (d/2) (expand _ W) 1 (offset b i.1,i.2):=by
    unfold views spark; apply Source.Hol.agree (I:=Set.Ioo (-1:ℝ) 2) (b:=0) isOpen_Ioo (convex_Ioo ..) (by simp) (A:=Source.partConnection (d/2) (expand _ W) 1 (offset b i.1,i.2)) _ (fun t _=>(A.solves ..).2 t) ((H.solves ..).1.trans (A.solves ..).1.symm) (show (1:ℝ) ∈Set.Ioo (-1:ℝ) 2 from ⟨by norm_num,by norm_num⟩)
    intro t H'; have he:=(H.solves c d (expand _ W) 1 (offset b i.1,i.2)).2 t; unfold Taper.connection at he; rw [house_p H.T b hx ht i.1 hi.1 i.2 t H',one_smul,one_pow] at he; exact he
variable (c B d)
abbrev Book (c:Side)(B:Type)(d:ℕ):= (Site c → su.Color) × Marker B d
variable {c B d}
abbrev Path (c :Side)(B : Type):= Directions su c × VectorD (Site c) B
local instance : NormedSpace ℝ (Snap su d) := inferInstance
local instance : NormedSpace ℝ (Book c B d):=inferInstance
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 680000
def mint (i:Edge (Site c)):Book c B d→L[ℝ] EdgeRead su (d/2):= LinearMap.toContinuousLinearMap {
   toFun X:=(X.1 i.1,X.1 i.1-X.1 (i.1+Lattice.step i.2),Place.road (Place.seat (offset b i.1)) i.2 X.2.1),map_add':=by intro x y; simp; abel,map_smul':=by intro r x; simp [smul_sub] }
def sealsZ (f: Site c → su.Color): Frame c:=fun i=> su.lieExp (f i)
def enroll (X: Book c B d): Path c B :=
   ((fun i=>logo (mint b i X)),hailC (sealsZ X.1) (scoring T b X.2.2))
omit hx ht
lemma seal_live :ContDiffAt ℝ ω (enroll (B:=B) (c:=c) (d:=d) T b) 0:=by
   apply ContDiffAt.prodMk; · apply contDiffAt_pi.mpr; intro i; exact (show ContDiffAt ℝ ω logo (mint (B:=B) b (d:=d) i 0) from by rw [map_zero]; exact logo_smooth ..).comp _ (mint b i (d:=d) (B:=B)).contDiff.contDiffAt
   obtain ⟨L,hL⟩:=scoring_cl T b (B:=B) (d:=d) (c:=c)
   let U(X:Book c B d):=scoring T b X.2.2 (c:=c); let f(X:Book c B d):=hailC (sealsZ X.1) (U X)
   have ht (x:Site c): ContDiffAt ℝ ω (fun X=>asks (f X) x) 0:=by
      simp_rw [f,hailF]
      let p(X:Book c B d) := (X.1 x,asks (U X) x)
      apply (ContDiff.contDiffAt (scaleG_live (B:=B))).comp (f:=p)
      apply ContDiffAt.prodMk
      · fun_prop
      apply askCL (B:=B) x |>.contDiff.contDiffAt.comp (f:=U); unfold U; rw [← hL]; exact L.contDiff.contDiffAt.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
   apply contDiffAt_pi.mpr; intro i; obtain ⟨⟨k,j⟩,rfl⟩:= (stretch (Site c)).surjective i
   exact contDiffAt_pi.mp (ht k) j
lemma seal_zero : enroll T b (0:Book c B d)=0:=by
    apply Prod.ext
    · funext i; change logo (mint b i (0:Book c B d))=0; rw [map_zero, logo_zero]
    obtain ⟨L,hL⟩:=scoring_cl T b (B:=B) (d:=d) (c:=c)
    change hailC _ (scoring T b (0:Lugs d B))=0; rw [← hL,map_zero]; exact Matrix.mul_zero _
include hx ht
lemma incAt : ∀ᶠ x:Book c B d in 𝓝 0,Lattice.Agrees (V:Set (Site c)) (increment 1 (enroll H.T b x).1) (gauge (sealsZ x.1) (views H b d x.2.1)):=by
   obtain ⟨A⟩:= Source.Hol.exists_ode su
   apply eventually_all.mpr; intro i; by_cases h: Mom.needed V i; swap; · exact Eventually.of_forall fun _ h₁ h₂=> False.elim (h ⟨h₁,h₂⟩)
   have hu : Tendsto (Place.peak (G:=su) (d:=d/2)) (𝓝 0) (𝓝 1):=by
       rw [← Place.peak_root su _]; exact ((su.continuous_mat.isClosedEmbedding su.mat_injective).isInducing.continuousAt_iff.mpr (Place.peak_smooth su _).continuousAt).tendsto
   have hv : Tendsto (mint (B:=B) b i (d:=d)) (𝓝 0) (𝓝 0):=by rw [← map_zero (mint (B:=B) (d:=d) b i)]; exact (mint b i).continuous.tendsto _
   filter_upwards [hv.eventually (hu.eventually su.plog_right)] with x hx'
   intro _ _; change su.lieExp (Place.logo _)*1=_; rw [mul_one,Place.logo,hx']; unfold Place.peak; let z:=x.1 i.1; let w:= x.1 (i.1+Lattice.step i.2); change su.lieExp z * flight _ 1 * (su.lieExp (z-(z-w)))⁻¹ = _; rw [sub_sub_cancel]; unfold Lattice.gauge; rw [traverse b hx ht H A x.2.1 i h]; exact congr_arg (fun p=>su.lieExp z * p * (su.lieExp w)⁻¹) (congr_fun (flight_test A (offset b i.1,i.2) x.2.1) 1)
end Pipes
end YM.Massive.Poised

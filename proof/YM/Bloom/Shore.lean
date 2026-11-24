import YM.Bloom.Choir
/-! # gauge underwriting at forecast pay horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom.TreeP
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit
open AnalyticBridge.LocalGaussianLaws.Current FreeResolvent
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G:Gauge}{c f:Side}{k m j B r n:ℕ}{X Y Z:Type}
variable (P Q:Parc)(p q:PlaqAxes)(x y:Cover)(i z:G.ColorIndex)
variable (U:Directions G c) {u v R W C a b d s t β:ℝ}
-- compare matrix for compressed forecast.
noncomputable def jetO (G:Gauge) (c:Side)(t:ℝ)(U:Directions G c): Matrix (Col G c) Unit ℂ:=Matrix.of fun i _=> ((t⁻¹*Fruit.jet U i:ℝ):ℂ)
lemma pockets (P:Matrix X (Col G c) ℂ)(i:X)(ht:cusp (P*radi G c) i≤ u)(h:‖U‖ ≤ s)(hp:|v⁻¹|≤ t):
     cusp (P*jetO G c v U) i ≤ t *(u*s):=by
    unfold jetO; rw [radial,Matrix.mul_smul,← Matrix.mul_assoc,cups_scale,Complex.norm_real]; apply mul_le_mul hp _ (cups_pos ..) ((abs_nonneg _).trans hp); exact cups_tender _ _ _ _ ((norm_nonneg _).trans h) _ ht (fun i=> by simpa only [cusp,Fintype.sum_unique] using (vector_rate U i).trans h)
lemma paid_turn (A:Matrix (Body k f) (Body m c) ℝ) : paid G A.transpose=(paid G A).transpose:= by unfold paid; rw [← FreeResolvent.tensor_transpose G A]; rfl
variable (g: Ratio c f) (J:Matrix (Exterior.Body 2 f) (Exterior.Body 2 c) ℝ)(F H:Bed)
noncomputable def heartP (H:Bed)(G:Gauge)(c:Side) := paid G (learned H c)
abbrev pop1 (W:Matrix Unit (Col G f) ℂ)(Z:Matrix Unit (Col G f) ℂ) (L:Matrix (Col G f) (Col G f) ℂ):= W*L*Z.transpose
noncomputable def treasureP (f:Side)(c:Side)(G:Gauge)(H:Bed)(R:Matrix (Col G f) (Col G c) ℂ) := R*heartP H G c*R.transpose
lemma shoresP : (pupil G f x p i P *treasureP f c G H (paid G J) * (pupil G f y q z Q).transpose) () ()= if i=z then ((pairP f (J*learned H c*J.transpose) x y (plaquette p) (plaquette q) P Q:ℝ):ℂ) else 0:=by
    unfold treasureP heartP; rw [← paid_turn,← hourly 0 0,←hourly 0 0]; exact coversU ..
lemma paid_low (hp:P∈tails k n)(ht:Q∈tails r m)(hj:n+2≤j)(hn:m+2≤j)(ha:0<a)(hb:0≤b) : ∃ C:ℝ,0≤ C ∧∀ {c f:Side}(x y:Cover)(p q:PlaqAxes)(i z:G.ColorIndex)(g: Ratio c f) (J:Matrix (Body 2 f) (Body 2 c) ℝ)(F H:Bed),Fare j a b g J F H →
     ‖pop1 (pupil G f x p i P) (pupil G f y q z Q) (treasureP f c G H (paid G J)) () ()‖ ≤ C/(g.count.val:ℝ)^(4+k+r):=by
    obtain ⟨C,hc,h⟩:=rivers P Q hj hn hp ht ha hb; refine ⟨C,hc,fun {c f} x y p q i z g J F H hf=>?_⟩; unfold pop1; rw [shoresP]; split
    · rw [Complex.norm_real]; exact h _ _ _ _ hf ..
    rw [norm_zero]; positivity
lemma paid_one : paid G (1: Matrix (Body k f) (Body k f) ℝ)=1:=by ext u v; rcases u with ⟨i,z,a⟩; rcases v with ⟨j,e,b⟩; unfold paid tensor; simp [Matrix.one_apply]; split_ifs <;> simp_all
lemma paid_full (hp:P∈tails k n)(ht:Q∈tails r m)(ha:0<a)(hd:0≤ d):∃ C:ℝ, 0≤ C ∧∀ (f:Side)(x y:Cover)(p q:PlaqAxes)(i z:G.ColorIndex) (F:Bed)(t:ℝ), Grain a t d F f →0<t → ‖pop1 (pupil G f x p i P) (pupil G f y q z Q) (heartP F G f) () ()‖ ≤ C:=by
      let j:= n+m+2
      obtain ⟨C,hc,h⟩:=paid_low (G:=G) (b:=d) P Q hp ht (j:=j) (by omega) (by omega) ha hd
      refine ⟨C,hc,fun f x y p q i z F t hV hx=>?_⟩; let I:=Bank.idle f; let M:= (1:Matrix (Exterior.Body 2 f) (Exterior.Body 2 f) ℝ); have hF: Fare j a d I M F F:= ⟨⟨_,_,Bank.TowerW.empty ..⟩,Row.rights _ _ hV.strip hx.le,⟨t,hx.le,hV.strip⟩,⟨_,hV.noteN,hV.noteN⟩⟩
      have hp: paid G M=1:=paid_one
      have he:= h x y p q i z _ _ _ _ hF; unfold treasureP at he; rw [hp] at he; simpa only [Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one, show (I.count.val:ℝ)=1 from Nat.cast_one,one_pow,div_one] using he
lemma mainR (l u:List Axis)(hn:10+k+m≤n)(ha:0<a)(ht:0<t)(hb:0≤ d)(hp:l.length ≤ k)(hr:u.length ≤ m)(hx: Rocky (some p) l k P)(hy:Rocky (some q) u m Q)(hv:0 < v)(w:ℝ) : ∃ C:ℝ,0 ≤ C∧∀ᶠ t':ℝ in atTop,∀ z':Cover,posT t' n z'∈ Oasis v w→∀ᶠ f: Side in atTop,∀ x y:Cover,∀ A : Bed,x-y=z'→ Grain a t d A f→
        t'*‖ (t'^n)^(4+l.length+u.length) • pop1 (pupil G f x p i P) (pupil G f y q z Q) (heartP A G f) () () - (legKernel (dollar l.length (p,l.get) i) (dollar u.length (q,u.get) z) (posT t' n z'):ℂ)‖ ≤ C:=by
     obtain ⟨C,hc,H⟩:=gauges (n:=n) l u p q hn ha ht hb hv w hp hr P Q hx hy; refine ⟨C,hc,?_⟩; filter_upwards [H] with t' ht' z' hv'; filter_upwards [ht' z' hv'] with f H x' y' A hu ht''; let s:=posT t' n z'; let F:=dollar l.length (p,l.get) i; let J:= dollar u.length (q,u.get) z
     rw [show ((legKernel F J (posT t' n z')) : ℂ) = (if i=z then Pic.stove (from_p p q) l u s else 0) from by simpa only [sub_zero] using gaugeWet (G:=G) s 0 p i l q z u (door hv' hv),pop1,pupil,pupil,heartP,coversU]; by_cases hp:i=z<;> simp only [hp,↓reduceIte]
     · -- p lifts mismatch proof irrelevance i turned into z? change
       exact H x' y' A hu ht''
     simpa
end YM.Bloom.TreeP
#print axioms YM.Bloom.TreeP.mainR
#print axioms YM.Bloom.TreeP.paid_full

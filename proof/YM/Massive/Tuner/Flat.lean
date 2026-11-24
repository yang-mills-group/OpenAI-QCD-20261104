import YM.QCD.Reef.Crown
import YM.QCD.Tide.Palace
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
namespace Reference
open IV
open NormedSpace
variable {u' τ₁ x₀ :ℝ}
lemma flatR (V:Voice c N)(f:Pixel c N)(p: PathData su)(w:SunR Ω)(v: BudgetPoint)(A:Clip)(Q:Train j)(hR:Rain.realP f) (h:f = u' • red V.P V.K w P₀ Q v p A z β τ₁ 0)(he: 0 <u'):
    (cBer f 1).re=u'*Real.exp (Finch.scent w.Z.page v p A β 0 N (1:Grid c))*Globe.pebble (paleF N (Globe.sunny P₀ Q c+ τ₁ • (1:Sheet c))+Patron.total V.P v.threshold 1):=by
    let F:= red V.P V.K w P₀ Q v p A z β τ₁ 0; have hx:(cBer f 1).re=‖cBer f 1‖:=( (congr_arg norm (hR 1).1).trans ((Complex.norm_real _).trans (Real.norm_of_nonneg (hR 1).2))).symm
    rw [hx,show cBer _ _ = u' • peakW c N (F 1) from ?_,norm_smul,Real.norm_of_nonneg he.le,mul_assoc];
    · let B:= FieldB Ω w c z P₀ Q ; unfold F red; change u' * ‖ber _ (Cove.light _ (scoreV V.P V.K v.threshold _ (B+(τ₁:ℝ) • 1) 1))‖=_; rw [poem]; rw [show (duo V.P V.K).bluff v.threshold 1= NormedSpace.exp (Cove.light _ (Patron.total V.P v.threshold 1)) from ?_,show (B+(τ₁:ℝ) • 1) 1 = Globe.sunny P₀ Q c+τ₁ • (1:Sheet c) from ?_]
      · let M:= Globe.sunny P₀ Q c+τ₁ • (1:Sheet c); let Z:= Patron.total V.P v.threshold 1; let W:=Finch.scent w.Z.page v p A β 0 N (1:Grid c); change u' * ‖ber _ (((Real.exp W:ℝ):ℂ) • (gauss (Lat.copies N M)* exp Z.val))‖ =_; rw [map_smul,norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,← Globe.oaks]; rfl
      · unfold B FieldB; simp only [blossomT, Pi.add_apply]; rw [Fork.pale _ (by decide), Fork.pale _ (by decide),add_zero,add_zero] ; rfl
      unfold Rise.bluff; rw [(Rails.heart ..).1,(Rails.heart ..).2, High.PrismT.bank _ _ _ (UVNext.CouplingReset.flags_one ..),mul_one, Cove.light_exp]
    unfold Rain.cBer; rw [show f 1=u' • F 1 from congr_fun h 1]; exact map_smul ((peakW c N).restrictScalars ℝ) ..

open Nola Globe

lemma pair_band (i : Modes c N) (w : ℝ) (n : ℕ) : band locationP (pair i) w n = w^2:=by
  classical
  let s : Keys c N := .inl i
  let t : Keys c N := .inr i
  have hne : s ≠ t := by simp [s,t]
  have ht : ∀ T : Support c, Nola.tell T 0=1:=fun j=> by simp [Nola.tell]
  change band _ (Grass.atom s * atom t) _ _=_
  rw [←mono_single, ←mono_single]
  rcases mono_mul_sign {s} {t} (by simp [hne]) with hp | hp
  · rw [hp, band_m]; simp [disjUnion_eq_union, Nola.edges,s,t,locationP,Nola.tell,Nola.reel]
  rw [hp,← neg_one_smul ℂ _,band_s,band_m]; simp [disjUnion_eq_union, Nola.edges,s,t,locationP,Nola.tell,Nola.reel]

lemma band_mass (y w : ℝ) (hw : 0 < w) (c : Side) (N : ℕ) (n : ℕ) :
    GrassA (paleF N (y • (1:Sheet c))) w n ((Fintype.card Fiber:ℝ)*N*|y| *w^2):=by
  classical
  change band _ (form (Lat.copies N ((y:ℂ) • (1:Sheet c)))) w n ≤ _
  rw [show Lat.copies N ((y:ℂ) • (1:Sheet c)) = (y:ℂ) • 1 from ?_]
  swap; · exact (Matrix.blockDiagonal_smul (y:ℂ) (fun _ : Flavor N => (1:Sheet c))).trans (by rw [show Matrix.blockDiagonal _= (1:Matrix (Modes c N) (Modes c N) ℂ) from copies_one N])
  rw [show Grass.form ((y:ℂ) • (1:Matrix (Modes c N) (Modes c N) ℂ)) = ∑ i, (y:ℂ) • pair i from ?_]
  swap; · simp [Grass.form,pair, Matrix.one_apply]
  apply (bandS _ _ _ hw).trans
  simp_rw [band_s, pair_band]; rw [sum_const,card_univ,nsmul_eq_mul]
  rw [Complex.norm_real,Real.norm_eq_abs]; simp only [Fintype.card_prod,Fintype.card_fin, Nat.cast_mul]; -- maybe
  ring_nf; exact le_rfl

-- all-steps (x becomes Level-of-that-step). Use imported flat Grass pressure
lemma flatBudget (κ t : ℝ) (U : ParcelR) (P : Plan 4) (hw : 0 < t) (c L : Side) (h : DomainF P N L c W) :
    ∀ᶠ y in atTop, ∀ (k : ℕ) (B : Side), B=c*L^k → ∀ (F : Voice B N) (p : BudgetPoint),
    Enn p b' L y t (1/8) (duo F.P F.K) → ∀ (Z : Pixel B N), Rain.realP Z → ∀ (G : Clip) (l : SunR U) (M : Train 4)
      (N' : PathData su) (β v z : ℝ), 0 < z → |v| ≤ roofK L t κ y →
      Z=z • red F.P F.K l P M p N' G (haloK L y) β v 0 →
    z * Real.exp (Finch.scent l.Z.page p N' G β 0 N (1 : Grid B)) * Globe.expo W B ≤ (cBer Z 1).re:=by
   obtain ⟨w,H,hw',hh,hH⟩:=h.port
   have hN:0 < N:=by have := b'.isLt; omega
   let d : ℝ := (Fintype.card Fiber:ℝ)*N*H^2
   have hc : 0 < H:=by linarith
   have hd : 0 < d:=by unfold d; positivity
   filter_upwards [honey (L:=L) b' hc (show 0 < w/2 by positivity) hw,(beamsR L t κ).below (by norm_num) (w/2/d) (by positivity)] with y hy hY k B hf F p he Z hZ G l M N' β v z hv hz hE
   rw [flatR P F Z _ l _ _ M hZ hE hv,Port.oneC,add_assoc]
   apply mul_le_mul_of_nonneg_left _ (mul_pos hv (Real.exp_pos _)).le
   obtain ⟨hx,hV⟩:=hy p B F he 1
   apply hH k _ hf
   · obtain ⟨f,g,h,-⟩:= he; exact Cocoa.add ((Tempo.one.smul v).butter N) (appetite F.P F.K h.pan hx)
   have ht: |v| ≤ w/2/d:= hz.trans ((le_abs_self _).trans hY)
   have hp := band_mass v H hc B N 6
   apply (band_add _ (paleF N (v • (1:Sheet B))).val (Patron.total _ _ _).val hc).trans ((add_le_add hp hV).trans _)
   have hh:= (le_div_iff₀ hd).mp ht; unfold d at hh; simp only [←mul_add]
   gcongr; linarith only [hh]
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.flatBudget

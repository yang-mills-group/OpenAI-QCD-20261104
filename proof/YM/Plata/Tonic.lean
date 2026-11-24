import YM.Plata.Dukes
import YM.Kly.Size
/-! pass seam bounds to spectral plane. Segments arbitrary number, mix adj and original. Later invert. -/
set_option maxRecDepth 6000
set_option maxHeartbeats 720000
set_option autoImplicit false
noncomputable section
namespace YM.Plata
open Function Set Filter Metric Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Plum Chess Cells
open Patria Patria.Depth Patria.Hub Patria.Exposure
open UV Needle
open YM.Fir Massive.Fir NoteF Tarn Choir Analysis
open Bridge (reflect Cluster carry Spread Chamber realize)
open Bridge.Kly (arcs Pack Car line stage Steady bloom)
open Massive.Fields (pointMoment)
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
variable {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}(hQ:Q.Harmony P φ) (T:Pollens P Q)
variable (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W)
variable {β ε:ℝ} (h:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop)
variable {I:Type*} [Fintype I]{m k n:ℕ} {u:ℝ} (z:I→ℂ) (w:I→List Bond)(hw: ∀ i, Strip.distinct (position (Q:=Q) (w i)))
variable {σ:ℝ}
set_option quotPrecheck false
local notation "Fnz"=>equip T A L
local notation "d₀" =>timeAxis
open Massive.Bridge.Kly (dotP M₀ M flight)
variable (s:Fin n→Bool)(V:Chamber (F:=equip T A L) Q.total timeAxis)(B:Spread V)
variable (H:Steady V)(E:Massive.Fields.Euclidean (F:=Fnz) Q.total)(hr:Involutive (T.adj timeAxis))
noncomputable abbrev nugget (i:I):Pack (equip T A L):= ⟨position (Q:=Q) (w i),hw i⟩
noncomputable abbrev pattern (x:I)(i:Fin n):Pack (equip T A L):= if s i then dotP (nugget T A L w hw x) else nugget T A L w hw x
noncomputable abbrev plan (f:Fin n→I): List (Pack (equip T A L)):= List.ofFn fun i=> pattern T A L w hw s (f i) i
-- bounds real motions
local notation "Kn" => Quorum n m
omit [Fintype I] in
private lemma floorP (i:Fin n)(k:ℕ)(F:Fin n→Fin (Quorum n m))(p:E4)(hv:0 < σ)(hp:‖p‖≤3*σ):let D:= ↑(i.val*k:ℕ)*(2*σ); let y:=Guilt (s i) d₀ p (notch p (i.val*k+(F i).val) σ d₀); D-3*σ≤ y d₀ ∧ y d₀ ≤ D+3*σ+↑(Quorum n m)*(2*σ):=by
       intro D y; have hz: p d₀≤3*σ∧-(3*σ)≤p d₀:=by
          have ht:= (PiLp.norm_apply_le p d₀).trans hp; rw[Real.norm_eq_abs,abs_le] at ht; exact ht.symm -- .symm?
       have hh :(↑(F i).val:ℝ)≤↑(Quorum n m):= by exact_mod_cast (F i).isLt.le
       unfold y Guilt notch D; cases h:s i<;> simp only[Bool.false_eq_true,↓reduceIte,PiLp.add_apply, Signed.mirrored,PiLp.smul_apply, show basis d₀ d₀=1 from by simp,↓reduceIte,smul_eq_mul,mul_one, Nat.cast_add]; all_goals (constructor<;>nlinarith [Nat.cast_nonneg (α:=ℝ) (F i).val])
end YM.Plata
namespace YM.Plata
open Function Set Filter Metric Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Plum Chess Cells
open Patria Patria.Depth Patria.Hub Patria.Exposure
open UV Needle
open YM.Fir Massive.Fir NoteF Tarn Choir Analysis
open Bridge (reflect Cluster carry Spread Chamber realize)
open Bridge.Kly (arcs Pack Car line stage Steady bloom)
open Massive.Fields (pointMoment)
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
open Massive.Bridge.Kly (dotP M₀ M flight)
local notation "d₀"=>timeAxis
lemma feeds {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}(hQ:Q.Harmony P φ) (T:Pollens P Q) (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W) {β ε:ℝ} (h:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop) {I:Type*} [Fintype I]{m n:ℕ} {u:ℝ} (z:I→ℂ) (w:I→List Bond)(hw: ∀ i, Strip.distinct (position (Q:=Q) (w i))) {σ:ℝ} (s:Fin n→Bool)(V:Chamber (F:=equip T A L) Q.total timeAxis)(B:Spread V) (H:Steady V)(E:Massive.Fields.Euclidean (F:=equip T A L) Q.total)(hr:Involutive (T.adj timeAxis))
 (hp:Available P φ w z u σ m)(hW:∀ i:I,Worn C φ (w i))(hs:0<σ): ‖∑ g:Fin n→I, wealth s z g * Bridge.Kly.stage B (plan T A L w hw s g)‖≤ u^n:=by
       let K:= Quorum n m
       choose F p hf hv using fun k:ℕ=> atP hQ h hP hφ z w s timeAxis (fun i=> i.val*k) T A L hp hW hr
       let d(i:ℕ)(j:Fin n):= j.val*i+(F i j).val; let D(i:Fin n)(k:ℕ):= Guilt (s i) d₀ (p k) (notch (p k) (d k i) σ d₀)
       let A'(g:Fin n→I):List (Car (equip T A L)):=List.ofFn fun i=>⟨pattern T A L w hw s (g i) i,D i⟩
       have he(g:Fin n→I): line (A' g):=by
           apply List.pairwise_ofFn.mpr; intro i j h; change flight (D i) (D j); let q:ℝ:= ((↑j.val:ℝ)-↑i.val)*(2*σ); have hq: 0 < q:=mul_pos (sub_pos.mpr (by exact_mod_cast h)) (by linarith)
           refine tendsto_atTop.2 fun b=>?_ ; filter_upwards [(Tendsto.atTop_mul_const hq (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (b+6*σ+ K*(2*σ))] with k hk
           let x:=D i k; let y:=D j k; change b ≤ y timeAxis-x timeAxis; have h1: x d₀≤↑(i.val*k:ℕ)*(2*σ)+3*σ+K*(2*σ):= (floorP s i k (F k) (p k) hs (hf k)).2
           have h2: ↑(j.val*k:ℕ)*(2*σ)-3*σ ≤ y d₀:= (floorP s j k (F k) (p k) hs (hf k)).1; change (↑k:ℝ)*q ≥ _ at hk; push_cast at h1 h2; unfold q at hk; nlinarith only[h1,h2,hk]
       have hw' (g:Fin n→I): List.map Prod.fst (A' g)= plan T A L w hw s g:=by unfold A' plan; rw[List.map_ofFn]; rfl
       have ht (g:Fin n→I)(k:ℕ): Bridge.Kly.all (A' g) k=vitality w s T A L d₀ (d k) (p k) σ g:=by
           simp only [A',Bridge.Kly.all,vitality,List.map_ofFn]; congr 2; funext x; cases h:s x<;> simp [pattern,lamp,D,h] -- arg reduction
       choose ha hb using fun g: Fin n→I=> arcs B H E (A' g) (he g)
       have hV(g:Fin n→I):Tendsto (fun k=> Strip.tone (vitality w s T A L d₀ (d k) (p k) σ g)) atTop (𝓝 (Bridge.Kly.stage B (plan T A L w hw s g))):=by
           unfold Bridge.Kly.stage; rw [← hw']; specialize hb g; simp_rw [ht] at hb; exact hb
       apply le_of_tendsto ((tendsto_finsetSum _ fun i _=> (hV i).const_mul (wealth s z i))|>.norm)
       filter_upwards [eventually_all.mpr ha] with i hi; exact hv i (fun g=> ht g i ▸ hi g)
end YM.Plata
#print axioms YM.Plata.feeds

import YM.Plata.Tonic
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
noncomputable abbrev Alk := ∑ i:I,z i • M₀ B (nugget T A L w hw i)
noncomputable abbrev aura (s: Bool)(w:B.algebra):B.algebra:=if s then star w else w
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
lemma expanded {Q:Choir}{C:Sequence}{P:Calibration C} (T:Pollens P Q) (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W)  {I:Type*} [Fintype I]{n:ℕ} (z:I→ℂ) (w:I→List Bond)(hw: ∀ i, Strip.distinct (position (Q:=Q) (w i)))  (s:Fin n→Bool)(V:Chamber (F:=equip T A L) Q.total timeAxis)(B:Spread V) (H:Steady V)(E:Massive.Fields.Euclidean (F:=equip T A L) Q.total)(hr:Involutive (T.adj timeAxis)) : (List.ofFn fun i:Fin n=>aura T A L V B (s i) (Alk T A L z w hw V B)).prod=∑ g:Fin n→I, wealth s z g • Bridge.Kly.starU B (plan T A L w hw s g):=by
        have he(i:Fin n): aura T A L V B (s i) (Alk T A L z w hw V B)=∑ j:I,turns (s i) (z j) • M₀ B (pattern T A L w hw s j i):=by
             unfold aura; cases h:s i; · simp only [turns,pattern,Bool.false_eq_true,↓reduceIte]; rw [h]; rfl -- check
             simp only [turns,h,pattern,↓reduceIte, Alk, star_sum,star_smul]; refine Finset.sum_congr rfl fun i _=>?_ ; exact congr_arg (star (z i) • ·) (Bridge.Kly.starM B H E hr _)
        simp_rw [he]; rw [planes]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Bridge.Kly.starU plan; rw[List.map_ofFn]; rfl
lemma awake {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}(hQ:Q.Harmony P φ) (T:Pollens P Q) (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W) {β ε:ℝ} (h:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop) {I:Type*} [Fintype I]{m n:ℕ} {u:ℝ} (z:I→ℂ) (w:I→List Bond)(hw: ∀ i, Strip.distinct (position (Q:=Q) (w i))) {σ:ℝ} (s:Fin n→Bool)(V:Chamber (F:=equip T A L) Q.total timeAxis)(B:Spread V) (H:Steady V)(E:Massive.Fields.Euclidean (F:=equip T A L) Q.total)(hr:Involutive (T.adj timeAxis))(hp:Available P φ w z u σ m)(hW:∀ i:I,Worn C φ (w i))(hs:0<σ): ‖inner ℂ V.omega0 (((List.ofFn fun i:Fin n=>aura T A L V B (s i) (Alk T A L z w hw V B)).prod).val V.omega0)‖≤ u^n:=by rw [expanded T A L z w hw s V B H E hr]; apply le_trans (Eq.le ?_) (feeds hQ T A L h hP hφ z w hw s V B H E hr hp hW hs); congr 1; let f (x:B.algebra):=inner ℂ V.omega0 (x.val V.omega0); let F:B.algebra→ₗ[ℂ] ℂ:={toFun:=f,map_add':=fun x y=> inner_add_right _ _ _,map_smul':=fun x y=>inner_smul_right _ _ _}; change F (∑ g:Fin n→I, wealth s z g • Bridge.Kly.starU B (plan T A L w hw s g))=_; rw[map_sum]; simp only[map_smul]; rfl
end YM.Plata
#print axioms YM.Plata.feeds
#print axioms YM.Plata.expanded
#print axioms YM.Plata.awake

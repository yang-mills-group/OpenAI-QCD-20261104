import YM.Fir.Scale
import YM.Lust.Ways
/-! Real derivative expenditures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators
variable {C:Sequence} {P:Calibration C} {β e:ℝ}(hp:C.Path β e) {n d:ℕ}
noncomputable abbrev aperture (C:Sequence) (U: Fin n→(i:ℕ)→stalk C i) (i:ℕ) (p:Strings n):ℂ:=readS C i (fun j=>U j i) p
noncomputable abbrev tube (C:Sequence) (U: Fin n→ (i:ℕ)→stalk C i)(z: Fin n) (V:(i:ℕ)→stalk C i)(i:ℕ)(p:Strings n):ℂ:= aperture C (Function.update U z V) i p
noncomputable abbrev eyeW (P:Calibration C)(D:Fin n→ℕ)(u: Fin n→Averaging) (i:ℕ)(p: Strings n): MultilinearMap ℂ (fun j=>Label (D j)) ℂ :=
    ((C.A i).regulator.average).compMultilinearMap ((MultilinearMap.mkPiAlgebraFin ℂ n _).compLinearMap fun j=> (LinearMap.proj (p j)).comp (stemV P (D j) i (u j))) -- check type
variable (U:Fin n→(i:ℕ)→ stalk C i)(V:(i:ℕ)→stalk C i)(z:Fin n)
lemma meters (i:ℕ)(p:Strings n):tube C U z V i p = Needle.GaugeP.readZ (C:=C) i z p (fun j=> U j i) (V i):=by
    apply congr_arg (fun u:Fin n→stalk C i=> readS C i u p); funext j; by_cases h:j=z; subst j; simp; rw [update_of_ne h,update_of_ne h]
lemma raises (b:Axis)(i:ℕ)(p:Strings n): let a:= C.S.spacing (C.N i); tube C U z (fun i=> lDer C i b (U z i)) i p = a⁻¹ • (aperture C U i (advanced z b p)-aperture C U i p):=by
    intro a; rw [meters]; let W:= Needle.GaugeP.readZ (C:=C) i z p (fun j=> U j i); let w:= U z i; let k:= step (S:=ℤ) b
    change W (((↑a:ℂ)⁻¹)• (shifting C i k w-w))= _; rw [map_smul,map_sub, ← Complex.ofReal_inv, Complex.real_smul]; congr 2
    · unfold W; apply congr_arg (fun v:(j:Fin n)→Insertion (C.S.side (C.R i) (C.N i)) 6=> ((C.A i).regulator.average) (List.ofFn v).prod); funext j; by_cases h:j=z
      · subst j; rw [update_self]; simp only [advanced,update_self]; rfl
      unfold advanced; rw[update_of_ne h,update_of_ne h]
    · unfold W; apply congr_arg (fun v=> readS C i v p); funext j; by_cases h:j=z; subst j; rw[update_self]; rw[update_of_ne h]
variable (G:∀ d,Cottage P d) (hr:Sway C.S) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) (x:Points n)(hx:x∈conf n)
abbrev air (F: Type*)[Norm F](p:ℕ→ F): Prop:=∃ C:ℝ,0 ≤ C∧∀ᶠ i in atTop,‖p i‖≤ C
noncomputable abbrev glass (G:∀ d,Cottage P d)(d:ℕ)(z:ℕ→ Stokes d→ℂ)(i:ℕ):stalk C i:= stem P d i ((G d).K.ridge i (z i))
include hr hp
lemma lively (d:ℕ) (z:ℕ→ Stokes d→ ℂ)(ht:air _ z): LightP C (glass G d z):=by
     obtain ⟨T,hT,H⟩:=ht; let K:=(G d).K; apply ((G d).pointsP hp hr none (fun i=> K.ridge i (z i)) _).1; exact ⟨K.heightM*T,mul_nonneg K.h_positive hT,(K.pluck.and H).mono fun i hi=>(hi.1 _).trans (mul_le_mul_of_nonneg_left hi.2 K.h_positive)⟩
include hφ hx
lemma forest (h:∀ k,LightP C (U k)) : ∃ B:ℝ,0≤B∧∀ᶠ p in Watch C φ x, ‖aperture C U (φ p.1) p.2‖≤B:=by
     obtain ⟨r,hr',hz⟩:= seascape hp hφ hx
     obtain ⟨L,hl,hP⟩:=torch hp hr U h r hr'; exact ⟨L,hl,(((hφ.comp beyond).eventually hP).and hz).mono fun i hi=> hi.1 _ hi.2⟩
omit hr
lemma snow (z':ℕ→Stokes d→ℂ)(h:Brush (G d).E (G d).K V z') (H:∀ k,k≠z→LightP C (U k)): Exposes C φ (fun i p=>tube C U z V (φ i) p - tube C U z (glass G d z') (φ i) p) x 0:=by
     apply Metric.tendsto_nhds.mpr; intro ε e; obtain ⟨r,hr',hz⟩:= seascape hp hφ hx; filter_upwards [(hφ.comp beyond).eventually (purseB hp U V d _ z H z' h r hr' (ε/2) (half_pos e)),hz] with p hp hz
     rw [dist_zero_right,meters,meters,←map_sub]; exact lt_of_le_of_lt (hp p.2 hz) (half_lt_self e)
include hr
lemma carbon (h:DimP C V)(H:∀ k,k≠z→LightP C (U k)):Exposes C φ (fun i=> tube C U z V (φ i)) x 0:=by
    apply Metric.tendsto_nhds.mpr; intro ε he; obtain ⟨r,hr',hz⟩:=seascape hp hφ hx; filter_upwards [(hφ.comp beyond).eventually (silver hp hr U V z H h r hr' (ε/2) (half_pos he)),hz] with p h hz; change dist (tube ..) 0 < _; rw [dist_zero_right,meters]; exact lt_of_le_of_lt (h p.2 hz) (half_lt_self he)
end YM.Massive.Fir
#print axioms YM.Massive.Fir.eyeW
#print axioms YM.Massive.Fir.raises
#print axioms YM.Massive.Fir.snow
#print axioms YM.Massive.Fir.carbon

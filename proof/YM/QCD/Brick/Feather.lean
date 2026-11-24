import YM.QCD.Brick.Flurry
/-! # The true nearest-history costs for transported spin-Cart probes (parent perspective) -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f:Side} {j k N m:ℕ}(B:Plan j)(F:Flight j k) (h:f.val=c.val*F.L.val){p r q t Z A :ℝ}
variable {R:Ratio c f}
lemma citizen (x:Site f)(z:Cover)(D:ℕ)(he:size z≤D) : (1+(separation (R.parent (x+wrap f z)) (R.parent x):ℝ))^2 ≤ (2+D*(R.count.val:ℝ)⁻¹)^2:=by
   let y:=x+wrap f z; let L:ℝ:=R.count.val; have hL :0<L:=Nat.cast_pos.mpr R.count.property
   have hx := Corona.foreshorten R y x; let d:ℕ:= separation (R.parent y) (R.parent x); have he:d*R.count.val ≤ D+R.count.val:=by
      rw [Nat.mul_comm]; exact hx.trans (Nat.add_le_add_right ((separation_comm ..).trans_le ((duration x z).trans he)) _)
   apply pow_le_pow_left₀ (by positivity); have hv : (d:ℝ)*L ≤ (D:ℝ)+L:=by unfold L; exact_mod_cast he
   change 1+(d:ℝ) ≤ 2+D*L⁻¹; have ht : (d:ℝ) ≤ D/L+1:= ((le_div_iff₀ hL).mpr hv).trans_eq (by rw [add_div, div_self (by positivity)])
   rw [← div_eq_mul_inv]; linarith
-- abstract rotor ray costs. Height argument relates Landmark h'/h; orientation anchored y. price r constant /L. 
variable {D:Type*}[Fintype D]{w:D→ℕ}
structure Lien (w:D→ℕ)(r t A:ℝ) (X:Cover→Alg D): Prop where
 poses (z) (v:ℕ):size z ≤ v → visc w t (X z)≤ A*(2+v*r)^2 ∧ dryL t (X z) ≤ A
 first (z) (v:ℕ): size z ≤ v → ∀ a, visc w t (gust X a z) ≤ A*r*(2+v*r)^2
 second (z) (v:ℕ): size z ≤ v→ ∀ a b,visc w t (gust (gust X a) b z) ≤ A*r^2*(2+v*r)^2
abbrev ply (F:Flight j k)(h:f.val=c.val*F.L.val):= proton F h
lemma fareP (C:ℝ)(ht:0<t)(hp:∀ x: Site f,∀ u:List Axis, u.length ≤2 →
      ∑ j,meets (sliceL F h) x 2 j *‖cell (oldDiff (ply F h) u) x j‖≤ C*cape F.L u.length)(v:ℝ)(hv:0 ≤ v)(hx:stemF N*C*cape F.L 0*t ≤ v) (o:Site f)(i:Accent N): Lien (Stew.lens ((sliceL F h).parent o)) (F.L.val:ℝ)⁻¹ t v (fun x=> loomQ o (ply F h) x i):=by
    let R:=sliceL F h; let W u:=oldDiff (ply F h) u; let f u x:= loomQ o (W u) x i
    let r:=(F.L.val:ℝ)⁻¹; have hr:0<r:=inv_pos.mpr (by positivity)
    let p z:=o+wrap _ z; let q z:= pitchQ (p z) i
    have hh (u:List Axis)(hu:u.length≤2)(x:Cover): Stew.plank (R.parent (p x)) t (f u x) ≤ v*r^u.length := by
       unfold f loomQ Stew.plank
       rw [vc_scale, pathLength,one_mul, show o+_=p x from rfl]; let Y:=tube N (W u) (q x)
       have hg := radiate (W u) (q x) (sliceL F h) (C*cape F.L u.length) (by unfold q; rw [residents]; exact hp _ _ hu) ht.le
       have hb:stemF N*(C*cape F.L u.length)*t≤ v*r^u.length:= (le_of_eq (show _=(stemF N*C*cape F.L 0*t)*r^u.length by unfold cape r; rw [pow_add]; ring_nf)).trans (mul_le_mul_of_nonneg_right hx (pow_nonneg hr.le _))
       have he:locationP (q x)=p x:=residents ..
       rw [he] at hg; exact hg.trans hb
    have hu (u:List Axis) (he:u.length≤2)(x:Cover)(L:ℕ)(hl:size x≤L): visc (Stew.lens (R.parent o)) t (f u x) ≤ v*r^u.length*(2+(L:ℝ)*r)^2:=by
       apply le_trans (b:=(1+(separation (R.parent (p x)) (R.parent o):ℝ))^2* Stew.plank _ t (f u x)) (trails (R.parent o) (R.parent (p x)) (f u x) ht.le)
       exact (mul_le_mul (citizen (R:=R) o x _ hl) (hh u he x) (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm ..)
    have hz u j: (fun x=> f (j::u) x)= gust (f u) j:=funext fun i=> lilt o i j _ (W u)
    refine ⟨fun z p₀ hj=> ⟨?_,?_⟩, fun z p₀ hj a=> ?_,fun z p₀ hj a b=>?_⟩
    · have h:= hu [] (by simp) z p₀ hj; rw [List.length_nil,pow_zero,mul_one] at h; exact h
    · have h:= (shot (Stew.lens (R.parent (p z))) _ t ht).trans (hh [] (by simp) z); rw [List.length_nil,pow_zero,mul_one] at h; exact h
    · have h:= hu [a] (by simp) z p₀ hj; rw [show List.length [a]=1 by simp,pow_one,show f [a] z=gust (f []) a z from congr_fun (hz [] a) z] at h; exact h
    have he := hu [b,a] (by simp) z p₀ hj; rw [show List.length _=2 from rfl, show f [b,a] z=gust (f [a]) b z from congr_fun (hz [a] b) z, show f [a]=_ from (show f [a]=gust (f []) a from hz [] a)] at he; exact he
end YM.QCD.Brick

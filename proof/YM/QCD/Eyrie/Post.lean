import YM.QCD.Eyrie.Clan

/-! # purchase inversion ticket before side -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Lat Finset
open Push.Uniform
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators ContDiff Classical
variable {n c f:Side}{X I K : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype I] [DecidableEq I] {A : K→Site f}{B : I→Site f}{L : K→ X}{q:ℕ}
  {r u b C D : ℝ}
lemma entries (F:X→Matrix I I ℂ) (h:glyph A L B B F r C)(hm:Multiplicity B q)
    (ht:0<u)(hp:4*(4*(4*u))≤r)(hC:0 ≤ C)(hD:0≤ D)
    (hR: IsUnit (F 0).det)(he:∀ i j, ‖(F 0)⁻¹ i j‖≤ D*Decay r (B i) (B j)):
    let K := 4*(C+C)*D*((q:ℝ)*countCost (4*(4*u)))
    let P := 4*K*K*((q:ℝ)*countCost (4*u))
    glyph A L B B (fun x=>(F x)⁻¹) u (4*D*(1+K+P)*((q:ℝ)*countCost u)):=by
  intro K P
  let W : Matrix I I ℂ:= (F 0)⁻¹
  let U:=fun x=> (F 0-F x)* W
  have hr:0<r:=lt_of_lt_of_le (by positivity) hp
  have hu:glyph A L B B (fun _=>W) r D:= fun i j=> (Flock.hush _ hr).patron (he i j)
  have hg:glyph A L B B (fun x=> F 0-F x) r (C+C):=by
    have hh:glyph A L B B (fun _=>F 0) r C:= fun i j=> (Flock.hush _ hr).patron (h i j).born
    simpa only [glyph, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg] using hh.plus h.minus -- defeq? need sub_eq_add_neg
  let v:=4*(4*u); let k:=4*u; have hv:0<v:=by unfold v; positivity
  have hk:0<k:=by unfold k; positivity
  have hh:glyph A L B B U v K:=hg.comp (hu.reduces hv (by change 4*v≤r at hp; linarith) hD le_rfl) hv hp hm (add_nonneg hC hC) hD
  have hK:0≤K:=by unfold K; have V':=count_pos hv; unfold v at V'; positivity
  have hx := hh.comp (hh.reduces hk (by change k≤4*k; linarith) hK le_rfl) hk (show 4*k≤v from le_rfl) hm hK hK
  have hV : glyph A L B B (fun x=>1+U x+U x*U x) k (1+K+P):= (((glyph.uni hk).plus (hh.reduces hk (by unfold k v; linarith) hK le_rfl)).plus hx) -- replace
  have hP : 0≤P:=by unfold P; have H:=count_pos hk; unfold k at H; positivity
  exact (jet_inv F (matrix_g fun i j=>(h i j).host) hR).redraw (hu.comp (hV.reduces ht (by change u≤4*u; linarith) (by positivity) le_rfl) ht (by linarith) hm hD (by positivity))
end YM.QCD.Eyrie

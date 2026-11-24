import YM.Massive.Papyrus.Avel
/-! # Hol observations under switches, including charge action.

Relative to TRUE untruncated image group & Snap space. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus
open Lattice Wilson RG Source Function QCD Source.Drops UV Filter Work.G05 Work.G06 Finset Matrix Labels
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
variable {h:ℕ}(k:Ortho)(s:Signed)(w:su.El)(H:Hol su)
abbrev gaugeF (g:Cover→su.El)(U:Land): Land:=Lattice.gauge g U
def scene (s:Signed)(x:Land): Land:= pull s 0 x
def night (x:Land):Land:= Massive.conjugate ∘ x
lemma scene_slide (s t: Signed)(x:Land) : scene s (scene t x)=scene (t*s) x:=by simp only [scene,pull_pull,affine,Signed.act_zero,add_zero]
lemma scene_gauge (g:Cover→su.El)(x:Land) : scene s (gaugeF g x)=gaugeF (fun i=>g (s.act i)) (scene s x):=by rw [scene,gaugeF, Work.G06.pull_gauge_zero]; rfl
lemma night_double : night ∘ night=id:=funext fun x=> funext fun i=> UV.conjugate_inv (x i)
lemma recol_el : conjugate (1:su.El)=1:= su.mat_injective (which_one true)
lemma colour_mul (u v:su.El): Lat.colour (u*v)=Lat.colour u* Lat.colour v:=rfl
lemma conj_el (p: su.El) : conjugate (w*p)=conjugate w*conjugate p:=su.mat_injective (which_mul true _ _)
lemma conj_rev : conjugate w⁻¹=(conjugate w)⁻¹:=eq_inv_of_mul_eq_one_left (by rw [← conj_el,inv_mul_cancel,recol_el]) -- conj notation `conjugate w⁻¹`
lemma night_scene(x:Land):night (scene s x)=scene s (night x):=by
    funext i; unfold scene night Lattice.pull Function.comp; unfold Step.read; split <;> simp_all [conj_rev]
lemma night_gauge (g:Cover→su.El)(x:Land) : night (gaugeF g x)=gaugeF (Massive.conjugate ∘ g) (night x):=funext fun i=>by simp only [gaugeF,Lattice.gauge,night,Function.comp_apply,conj_el, conj_rev]
namespace Scan
abbrev trunkJ (h:ℕ) (H:Hol su)(x:Snap su h): Land:=H.links h (expand h x) 1
def send (φ:(i:ℕ)→Module.End ℝ (Labels.Taylor su i))(h:ℕ): Snap su h→L[ℝ]Snap su h:= LinearMap.toContinuousLinearMap (LinearMap.pi fun i=> (φ i.val).comp (LinearMap.proj i))
lemma sendJet (φ:(i:ℕ)→Module.End ℝ (Labels.Taylor su i))(x:Snap su h): changedJet φ (expand h x) = expand h (send φ h x):=by funext i; unfold changedJet expand; split; rfl; simp -- `simp`
abbrev tinted (u:su.El)(h:ℕ):= send (fun _=>Taylor.paint u) h
abbrev recol (h:ℕ):= send (fun _=>UV.recolor) h
abbrev rot (k:Ortho)(h:ℕ):= send (fun _=>Taylor.turn k) h
lemma rot_mul (v:Ortho)(x:Snap su h) : rot k _ (rot v _ x)=rot (k*v) _ x:= funext fun _=>(Taylor.turn_mul k v _).symm
lemma rot_unit(x:Snap su h):rot 1 _ x=x:=funext fun _=> Taylor.oneTurn _
lemma rot_paint(x:Snap su h):rot k _ (tinted w _ x)=tinted w _ (rot k _ x):=funext fun _=> (Taylor.turn_paint k w _).symm
lemma value_R (x : Labels.Taylor su h)(i:Axis)(w:E4): Taylor.value (UV.recolor x) i w= UV.reflectColor (Taylor.value x i w):=rfl
lemma recol_rot (x:Snap su h): recol _ (rot k _ x)=rot k _ (recol _ x):=by
    funext i; change UV.recolor (Taylor.turn k _)= Taylor.turn k (UV.recolor (x i)); apply Taylor.value_ext; funext a x; rw [value_R,Taylor.turn_value,Taylor.turn_value,map_sum]; simp only [value_R,map_smul]; rfl
lemma recol_paint (x:Snap su h) : recol _ (tinted w _ x) = tinted (Massive.conjugate w) _ (recol _ x):=funext fun _=> UV.repaints ..
lemma recol_back (x:Snap su h) : recol _ (recol _ x)=x:=funext fun _=> UV.recol_inv _
lemma landscape (x:Snap su h) : trunkJ h H (rot s.ortho⁻¹ h x)=scene s (trunkJ h H x):=by
    unfold trunkJ rot; rw [← sendJet]; exact (Work.G01.swirls_of_flow H s h ..).symm
lemma panorama (x:Snap su h) : trunkJ h H (tinted w h x)=gaugeF (fun _=>w) (trunkJ h H x):=by
    unfold trunkJ tinted; rw [← sendJet]; exact Work.G01.links_colored ..
lemma spec (X:Mat): star X.transpose=Mstar X:=rfl
/-- real linear -/
def Mconj : Mat →L[ℝ] Mat:= LinearMap.toContinuousLinearMap
                 { toFun:= fun x=> Mstar x
                   map_add':=by intro x y; ext; simp [Mstar]
                   map_smul':=by intro c x; ext; simp [Mstar] }
lemma Mconj_apply (x:Mat): Mconj x=Mstar x:=rfl
lemma conj_flow {u:ℝ→su.El}{f:ℝ→su.Color}(h:Source.SolvesLink u f): Source.SolvesLink (fun i=>conjugate (u i)) (fun i=>UV.reflectColor (f i)):=by
    refine ⟨by simp [h.1,recol_el],?_⟩; intro t
    have ht(m:ℝ) : HasDerivAt (fun i=> Lat.colour (u i)) (Lat.colour (u m) * (show Mat from su.colorMat (f m))) m:= h.2 m
    have he:= Mconj.hasFDerivAt.comp_hasDerivAt t (ht t); apply he.congr_deriv; let U:=Lat.colour (u t); let S:Mat:=su.colorMat (f t); rw [UV.reflMat]; exact mstar_mul U S
lemma spectrum (x:Snap su h) : trunkJ _ H (recol _ x)=night (trunkJ _ H x):=by
    unfold trunkJ recol; rw [← sendJet]; funext i; let J:=expand h x; let L:=changedJet (fun _=> UV.recolor) J
    have he : partConnection h L 1 i=fun p=>reflectColor (partConnection h J 1 i p):=by funext t; unfold L partConnection potential changedJet; rw [map_smul,map_sum]; simp only [value_R] -- forms
    exact congr_fun ((H.solves h L 1 i).unique (he.symm ▸ conj_flow (H.solves h J 1 i))) (1:ℝ)
end Scan
end YM.Massive.Papyrus
#print axioms YM.Massive.Papyrus.Scan.spectrum

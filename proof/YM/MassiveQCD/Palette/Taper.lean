import YM.MassiveQCD.Palette.Doors
import YM.MassiveQCD.Palette.Rates
import YM.MassiveQCD.Palette.Eligibility
import YM.QCD.Stem.Creds
/-! # Through-three projection out of the perturbed columns
 Capture one base term, at its OWN masks; Y entries retain exact supports & payments.
 No fictitious translation on unreadable supports. When ready to publish at
 a single power in the charged-expansion, pack all Ready columns according to this
 projection BEFORE symbolics. Activate the rank-two capture via Bool (power one used
 in the proof). The resulting heated corrections must still be purchased as additional
 analytic soft or unit shifts; no cheap operation across bar masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ η ξ :ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {ι:Type}(E:Gem c N ι)
noncomputable def gemTone (i:ι): ℝ:= -(Reggae.river c N (E.view i 1))
-- if false this projector only removes the body at EACH power
noncomputable def photon (z:Bool)(i:ι):Flavor N→Spike:= if z then fun b=> lane E b i none else 0
noncomputable def spinCharge (z:Bool)(i:ι):EvenA c N:=beam (E.addr i).site (photon E z i)
noncomputable def peak (z:Bool)(i:ι): EvenA c N:= baker c N (gemTone E i)+spinCharge E z i
variable (z:Bool)(s : Strut c)(g:Site c→ℂ)(k:Spike)(e:Equiv.Perm ι)(i:ι)
lemma era (h:E.addr (e i)=rotateL (E.addr i) s)(hV:∀ V:Grid c,Diode N s k g (E.view i (sky s V))= E.view (e i) V)
    (hv:Noted E) (he:Warrant s g k)(hG:Gated (E.addr i).support (E.view i 1)): gemTone E (e i)=gemTone E i∧ spinCharge E z (e i)= Diode N s k g (spinCharge E z i) :=by
    refine ⟨?_,?_⟩
    · unfold gemTone; rw [←hV,show sky s 1=(1:Grid c) from ?_]; congr 1; exact mur _ _
      ext1 i; simp [Strut.sky,pull,Step.read]
    unfold spinCharge; rw [h,flashTwist _ s _ _ _ he]; apply congr_arg (beam _); unfold photon; split
    · funext j
      have hf:= Phased.whirl j _ _ _ none he (hv.num _ _) hV (hv.gauge _) hG; rw [show skySig s.1 none=1 from rfl, one_smul,show tide s.1 none=none from rfl] at hf; unfold lane; rw [h]; exact hf -- defeq
    funext b; change _= k*(0: Spike)*_; simp
set_option maxHeartbeats 620000 in
lemma rank_ink (h:Noted E): shadeG (fun _:Grid c=> peak E z i) ∧ Regal c N (peak E z i)=peak E z i ∧ AccentFit (peak E z i):=by
    unfold peak spinCharge
    refine ⟨fun V g=> ?_,?_ ,fun V hV=>?_⟩
    · refine congr_arg Subtype.val (Eq.trans (map_add (sways (Lat.rotates N g)) (baker c N (gemTone E i)) _) (congr_arg₂ (·+·) (Reggae.through ..) (Subtype.ext (flashColor (E.addr i).site (photon E z i) V g))))
    · rw [map_add,flashStar,Reggae.through]; apply congr_arg; apply congr_arg; funext b; unfold photon; split
      next hz=> exact Eq.symm (Phased.headQ b (E.addr i) (E.view i) none (h.num i _) (h.gauge i) (h.real ..))
      next _=> simp
    rw [map_add,Reggae.through]; exact congr_arg _ (pageK _ _ hV) -- synt
lemma cornerRank : Gated {(E.addr i).site} (peak E z i):=by
    let A:Support c:={(E.addr i).site}; let V:=beam (E.addr i).site (photon E z i)
    let T := (light (Keys c N)); change T (_+V)∈ _; rw [map_add]; exact Subalgebra.add_mem _ (Reggae.gates ..) (flashPad (photon E z i) (U:=A) (mem_singleton_self _)) -- B? implicit U
lemma resSeek (he:Regal c N (E.view i 1)=E.view i 1): mud (E.view i 1-peak E z i)=0:=by
    unfold peak; change clay c N (_-_) = _; rw [map_sub,map_add (clay c N)]; change mud (E.view i 1) - (mud (baker c N _)+ mud (spinCharge E z i))=0; rw [gives,gemTone, show mud (spinCharge ..)=0 from plankGrade (fun j=> _), realP he]; simp [Complex.ofReal_neg]
lemma shapeRank (hw:Nonwrapping (E.addr i).support (E.addr i).site) (b:Flavor N): shape (E.addr i).site (feeF b (E.view i 1- peak E true i)) none=0:=by
    let o:= (E.addr i).site
    change profile o none (meter b (_- (_+_)))=0; rw [map_sub,map_add,show meter b (baker c N _)=0 from reducible b _,zero_add,map_sub]
    change _-shape o (feeF b (beam o _)) none=0; rw [flashAt]; unfold photon lane mote; rw [if_pos (show (true:Bool)=true from rfl),if_pos hw]; exact sub_self _
noncomputable def shadowE (z:Bool): Gem c N ι:= ⟨E.addr, fun i V=> E.view i V-peak E z i⟩
lemma shut : AccentFit (spinCharge E z i):= pageK _
lemma shutter (h:Noted E): Noted (shadowE E z):=by
    have he(i):= rank_ink E z i h
    exact ⟨fun i V k=> congr_arg Subtype.val (Eq.trans (map_sub (sways (Lat.rotates N k)) _ (peak E z i)) (congr_arg₂ (·-·) (Subtype.ext (h.gauge i V k)) (Subtype.ext ((he i).1 V k)))), fun i U g hv=> Eq.trans (map_sub (sways (flute _ g)) _ _) (congr_arg₂ (·-·) (h.num i U g hv) ((he i).2.2 g hv)),fun i U=>Eq.trans (map_sub (Regal c N) _ _) (congr_arg₂ (·-·) (h.real i U) (he i).2.1)⟩
lemma rank_ray (h:E.addr (e i)=rotateL (E.addr i) s)(hV:∀ V:Grid c,Diode N s k g (E.view i (sky s V))= E.view (e i) V) (hv:Noted E) (he:Warrant s g k)(hG:Gated (E.addr i).support (E.view i 1))(V:Grid c): Diode N s k g ((shadowE E z).view i (sky s V))=(shadowE E z).view (e i) V:=by
    obtain ⟨hG,hk⟩:= era E z s g k e i h hV hv he hG; change Diode _ _ _ _ (_-_) = _ - peak ..; unfold peak; rw [map_sub,map_add, Reggae.through,hV, hk, hG]
lemma tempo (hz:0 ≤ u)(hp:∀ (c:Side) (N:ℕ)(b:Flavor N)(i: Site c)(X:EvenA c N)(j: SampleX)(w:ℝ), 0 ≤ w→ w^2 * ‖shape i (feeF b X) j‖ ≤ u*Sen i w X) (h:0<t)(hh:Woven (E.addr i).site (E.addr i).support p t (E.view i) r):
    ‖(gemTone E i)‖ ≤ r ∧ Woven (E.addr i).site {(E.addr i).site} p t (fun _=>spinCharge E z i) ((stampFee N*u)*r) ∧
    Woven (E.addr i).site (E.addr i).support p t ((shadowE E z).view i) ((stampFee N*u+2)*r) :=by
    let B:= (E.addr i).support; let o:= (E.addr i).site; let C:Support c:={o}; let τ:= gemTone E i; have hk : ‖τ‖≤r:=(norm_neg _).le.trans ((sees o _ h.le).trans (hh.sizeU _ (flat_ok ..)))
    have ht:0 ≤ stampFee N:= zero_le_one.trans stampFound; let U:= stampFee N*u
    have hF:= stamped o h (photon E z i) p; have hX : t^2*‖photon E z i‖ ≤ u*r:=by
       unfold photon; split
       · exact postK E hz hp _ h i hh
       rw [norm_zero,mul_zero]; exact mul_nonneg hz hh.travel
    let P:=spinCharge E z i; have hL: Woven o C p t (fun _=>P) (U*r):= hF.stretches (Subset.refl C) ((mul_le_mul_of_nonneg_left hX ht).trans_eq (mul_assoc ..).symm)
    have hx:C⊆ B:= singleton_subset_iff.mpr (E.addr i).anchor
    refine ⟨hk,hL,?_⟩
    have hK:= (constChoice o (baker c N τ) r t C p ((vine o τ t h.le).trans_le hk) (Reggae.gates C τ)) -- Borel wrong parameter
    have he:= hh.addition ((((hK.addition hL).byScalar (-1)).stretches hx le_rfl))
    rw [norm_neg,norm_one,one_mul,neg_one_smul, ← sub_eq_add_neg] at he -- defeq functions
    refine he.stretches (Subset.refl _) (le_of_eq (by unfold U; ring))
end YM.QCD.Stew.Phased

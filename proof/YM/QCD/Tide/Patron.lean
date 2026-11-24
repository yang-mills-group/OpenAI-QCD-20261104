import YM.QCD.Tide.Easy
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {i j:ℕ} (P:Flight i i)(hf:f.val=c.val*P.L.val){t:ℝ}
lemma stage (x:Stud c F): stampC (tallH R x) t = tallH R (stampC x t):=by
     funext i; let S:=Lat.copies F (lens R); let X:= x (R.pullC su i); rw [stampC,huesT,huesT]; change engine _ _ (tilt S X)=tilt S (engine _ _ X); rw [← write X,map_sum,map_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=> ?_; simp only [map_smulₛₗ,map_smul]
     rw [nominate (mono i) t _ (homogeneous i), nominate (tilt S (mono i)) t i.card (exterior_layer _ (turn_deg (homogeneous i))),map_smulₛₗ]; simp
lemma stageS (X:Set (Site c))(x:Stud c F)(h:Uses X x): Uses X (stampC x t):=by
    refine ⟨fun U V he=> congr_arg (patternC _ _ _) (h.1 U V he),fun U=>?_⟩; obtain ⟨P,hp⟩:=h.2 U; unfold stampC; rw [hp]; refine ⟨engine t _ P,?_⟩; rw [← write P,map_sum,map_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=>?_ ; unfold patternC; rw [map_smul,map_smul,map_smul,map_smul,nominate (mono i) t _ (homogeneous i)]; rw [map_smul]; exact congr_arg ((coef i P) • ·) (nominate (Grass.pass (setDay X) (mono i)) t i.card (pass_layer _ (homogeneous i)))
lemma stageN (x:Stud c F)(h: Neutral x): Neutral (stampC x t):=by
    intro U V; unfold stampC; rw [show slots F U _= patternC _ _ t (slots F U (x (gauge U V))) from pitcher ..,h]
noncomputable def look (P:Flight i i)(K:KernelChoices)(hf:f.val=c.val*P.L.val)(β t:ℝ)(x:Stud c F): Stud f F:= offer P K hf β (stampC x t⁻¹)
lemma lookup (h:P.patch.Branches K su)(x:Stud c F)(hx: Stays x): Stays (look P K hf β t x):=offers P hf h _ (paysA x hx)
lemma pills (h:P.patch.Branches K su)(x:Stud c F)(hx:Stays x)(H:Neutral x)(hp:Uses (eaves R (longM P.patch)) x):let T:= gateH R (sliceL P hf); let y:=look P K hf β t x
    Uses (eaves T (longM P.patch)) y∧ Neutral y:=by
      intro T y; let M:=stampC x t⁻¹; have he:= paysA (t:=t⁻¹) x hx; exact ⟨offerL P hf h M he _ _ (stageS _ x hp) (fun _ hu=> struts P hf _ hu), rolly P hf h M he (stageN x H)⟩
lemma prices (h:P.patch.Branches K su)(x:Stud c F)(hx:Stays x)(hh:Uses (eaves R (longM P.patch)) x)(he:R.kind=.link): look P K hf β t (tallH R x*x) = tallH (gateH R (sliceL P hf)) (look P K hf β t x)*look P K hf β t x:=by
     let Z:=tallH R x; let X:=eaves R (longM P.patch); let V:= R.reflect '' X; have hp: Disjoint V X:= Set.disjoint_left.mpr (by rintro i ⟨x,hx,rfl⟩ H; exact R.link_switch he (eaveH _ he hx) (eaveH _ he H)); have hz:=tallSite (R:=R) x X V hh (Set.mapsTo_image ..); unfold look; rw [show stampC (tallH R x*x) t⁻¹=stampC (tallH R x) t⁻¹*stampC x t⁻¹ from funext fun i=>map_mul _ _ _, acrossH _ _ h V X _ _ (paysA _ (tallCost x hx)) (paysA _ hx) (stageS V Z hz) (stageS X x hh) hp,stage, ← utter P hf h (stampC x t⁻¹) (paysA x hx) he]
structure Healing (J:Patch)(Y:Pixel c F): Prop where
    rails (R:Cells.Cut c) (h:R.kind=.link)(hp: 2 ≤ R.half.val)(x: Stud c F)(hx:Stays x)(hz: Neutral x)(he:Uses (eaves R (longM J)) x):0 ≤ fresh Y (tallH R x*x)
lemma health (h:P.patch.Branches K su)(X:Pixel f F)(Y: Pixel c F)(hX:Healing P.patch X)(ht:0<t)(hx:Continuous X)(hv:Modern P K hf β t X Y): Healing P.patch Y:=by
      constructor; intro R hR he x hp hL hw; let T:= gateH R (sliceL P hf); let u:= look P K hf β t x; obtain ⟨hu,hz⟩:= pills P hf (β:=β) (t:=t) h x hp hL hw
      rw [pov P hf X Y h ht hv _ ((tallCost x hp).mult hp) hx]; change 0 ≤ fresh X (look P K hf β t _); rw [prices P hf h x hp hw hR]; have he':2 ≤ T.half.val:= he.trans (le_mul_of_one_le_right (by omega) (P.L.property)); exact hX.rails T rfl he' u (lookup _ _ h x hp) hz hu
end YM.QCD.Tide

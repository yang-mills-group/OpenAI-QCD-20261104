import YM.QCD.Villa.Salute
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Villa
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Cove Leaf Lat Creek Loom
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass Sway OrbitG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {Y:StepData c f} {η p h z a a' t v u u' q:ℝ} {D E J:Type}[Countable E][Countable J][Fintype D]
variable {T : Tube su Y} {W' :ℕ→Atom su 2} {P':Plan k} {L:Side}
variable (H:Cash W τ μ L Q o C T (trimP T R δ β b))
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
local notation "B" => radiusB τ
local notation "π'"=> trimP T R δ β b
open Extra Sway OrbitG Bay Strut Revolve
local notation "S"=>Y.ratio
open scoped Matrix
variable {L': Grid c → Sheet c}{Γ: Land c (Site c) (Site c)} {V:Pays c (Site c) (Site c)}{σ:ℝ}
local notation "P'"=> sailP H Γ N
variable (h₀ : Run.Pack id id σ h l L' a Γ V)
lemma chalkP (hp: Torch Γ) (U:Grid c)(x:Site c)(z:XMark c): (sheetP Γ B (x,z) U)=foldH (sheetP Γ B (x,z) U):=by
   let G:=singleR c; unfold sheetP; dsimp only; apply whist; intro i j; unfold foldH; nth_rw 2 [← terraJ (D:=Site c)]; rw [stack]; unfold terraL; rw [cell_ride_right,cell_ride_left,cell_flip, Equiv.refl_apply, Equiv.refl_apply,stack, cT]; unfold sale; simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul]
   congr 1
   · split_ifs <;> norm_num
   have he a' b' z : Γ a' b' z (Kit.settled U)= _:= congrFun (congrFun (congrFun (congrFun hp.2.symm a') b') z) (Kit.settled U)
   simp only [seed,fullT] at he
   cases z with
   | none=> unfold chipK; simp only [spoon,Finset.sum_apply,star_sum,Matrix.mul_sum,Matrix.sum_mul]; exact sum_congr rfl (fun p hp=> he _ _ p)
   | some z=> simp only [chipK]; split; exact he _ _ _; simp
lemma polarP (W: OrbitG (Modes c N)) (q: Site c→su.El) (hv:∀ i U V, W.passL (dropG N Γ Y.ratio B i (Lattice.gauge (constantGauge q Y.ratio) U) (Lattice.gauge q V))= dropG N Γ Y.ratio B i U V) : (sailP H Γ N).sings q W.passL:=by
   refine ⟨phare W,fun i X V=>?_⟩; change W.passL (NormedSpace.exp _-1)= NormedSpace.exp _-1; rw [map_sub,map_one,NormedSpace.map_exp W.passL W.phare,hv]
lemma horn (hp: Torch Γ): (P').sings (fun _=>1) (dawn (idol c N)).passL:=by -- macro
   apply polarP; intro i U V
   rw [presenceP,show constantGauge (fun _=> (1:su.El)) Y.ratio=fun _=>1 from rfl,presenceP]
   apply Subtype.ext
   let W:=-(sheetP Γ B i V-sheetP Γ B i (lowC Y.ratio U))
   have he:W=foldH W:=by
      have hv: ∀ U:Grid c,sheetP Γ B i U = terraL (Site c)*(sheetP Γ B i U)ᴴ*terraL (Site c) := fun U=> chalkP hp U i.1 i.2; unfold W foldH; rw [Matrix.conjTranspose_neg,Matrix.conjTranspose_sub,Matrix.mul_neg,Matrix.mul_sub, Matrix.neg_mul,Matrix.sub_mul,← hv,← hv]
   let Y:=idol c N; change disguise Y (surf _ (form (Lat.copies N W)))=form (Lat.copies N W); rw [surf_form,show star (Lat.copies N W)= Y*Lat.copies N W *star Y from (copies_star ..).symm.trans (duality N he).1, disguise,form_map, Matrix.transpose_transpose]; have hx: star Y*Y=1:=white.1; simp only [Matrix.mul_assoc,hx,mul_one]; rw [← Matrix.mul_assoc (star Y),hx,one_mul]
lemma ribbon (W:Matrix (Flavor N) (Flavor N) ℂ)(hv:W∈unitary _): (sailP H Γ N).sings (fun _=>1) (trade (flute (Lat.Row c) W)).passL:=by
   apply polarP; intro i U V; rw [presenceP,show constantGauge (fun _=> (1:su.El)) Y.ratio=fun _=>1 from rfl,presenceP]; apply rayTrade _ (unit_f hv); simp_rw [← replicas]; rw [column,Matrix.mul_assoc, (unit_f hv).2,Matrix.mul_one]
include h₀ in
lemma mesh (z:Site c→su.El) : (P').sings z (trade (rotates N z)).passL:=by
   apply polarP; intro i U V; apply rayTrade _ (rotates_law ..)
   let W:=siteRot z
   have he p:sheetP Γ B i (Lattice.gauge z p) = W*sheetP Γ B i p *star W:=by
      apply whist; intro x y; unfold W siteRot sheetP; rw [stack,cell_ride_right,cell_ride_left,stack,monotype]; rw [(cups h₀ i.1 x y B i.2).2.2.2.2.2 p z]; simp only [sale,Matrix.mul_smul,Matrix.smul_mul]; rfl
   rw [framed_c, show constantGauge z Y.ratio ∘ Y.ratio.embed=z from funext fun i=>congr_arg z (Y.ratio.embed_parent i),he,he,← Matrix.sub_mul,← Matrix.mul_sub,← Matrix.neg_mul,← Matrix.mul_neg]; exact Sway.podium ..
include h₀ in
lemma visible (hs:0<σ): (P').speaking:=by
    intro i
    have hf:Continuous (sheetP Γ B i):=by
       refine continuous_pi fun x=>continuous_pi fun y=>?_ ; unfold sheetP batch; simp_rw [monotype]; have he:= Jets.Sun.breeze (cups h₀ i.1 x.1 y.1 B i.2) hs
       have ht :Continuous (fun U:Grid c=> sale i.1 x.1 y.1 (chipK i.1 B Γ x.1 y.1 i.2 (Kit.settled U))):= he.const_smul (_:ℂ)
       exact (continuous_apply y.2).comp ((continuous_apply x.2).comp ht)
    let f' (x:Grid f×Grid c):= dropG N Γ Y.ratio B i x.1 x.2
    have hp: Continuous (lowC Y.ratio):=by unfold lowC; fun_prop
    have hV: Continuous (fun x:Grid f×Grid c=> f' x|>.val):= by
       have he:= (continuous_copies N (i:= Lat.Row c)).comp (((hf.comp continuous_snd).sub (hf.comp (hp.comp continuous_fst))).neg)
       change Continuous (fun x:Grid f×Grid c=> ∑ i', ∑ j,(Lat.copies N (-(sheetP Γ B i x.2-sheetP Γ B i (lowC Y.ratio x.1))) i' j) • (_*_)); exact continuous_finsetSum _ (fun a _=>continuous_finsetSum _ (fun b _=>(((continuous_apply b).comp ((continuous_apply a).comp he)).smul (continuous_const (y:=Grass.psi b * Grass.bar a)))))
    have hf':Continuous f':= hV.subtype_mk _
    exact ((NormedSpace.exp_continuous.comp hf').sub continuous_const).measurable
local notation "G"=> singleR c
lemma hygiene (s: Strut c): raise (singleR c) s=s:=Prod.ext rfl (monotype _)
lemma ruler (T: Strut c)(i : Gaze c) (b:ℕ) (Y:StepData c f):let E:= Y.ratio; let p:=Equiv.prodCongr (act T) (hoops (singleR c) T) i
                                                           plank (sashP p b) E b=(plank (sashP i b) E b).image (act T) :=by
   intro U p
   have hf := Port.pump (T:=singleR c) (Sum.inl i) T b
   change (punch i.1 b i.2).image (Strut.act (raise G T)) = punch (act (raise G T) i.1) b (hoops G T i.2) at hf -- maybe pump ambiguous
   rw [hygiene] at hf; unfold Loom.plank; rw [show sashP p b=(sashP i b).image (affine T.1 T.2) from ?_]
   rotate_left
   · exact hf.symm
   let Z:= sashP i b
   have hx : (rig U (Z.image (affine T.1 T.2))).image U.parent=((rig U Z).image U.parent).image (affine T.1 T.2):=by
      rw [parent_image (Y:=Y)]; apply congr_arg (fun i:Support f=> i.image U.parent); unfold rig; rw [← halo_image]; exact congr_arg (Lattice.halo _) (by rw [image_image,image_image]; exact image_congr (fun i _=> (peaks T U i).symm))
   rw [hx, ← image_union, halo_image]; rfl
lemma cache (hp:Torch Γ)(t: Signed)(b':Site c)(χ:Site c→ℂ)(q:Spike)(hh: Warrant (t,b') χ q)(π:(trimP T R δ β b).activities.Moves t (Y.ratio.embed b')):
   let p:=(t,b'); Fleet.Marches (sailP H Γ N) π (Equiv.prodCongr (act p) (hoops G p)) (trade (Lat.copies N (haze p q χ))).passL:=by
   intro p; let V:=Equiv.prodCongr (act p) (hoops G p)
   refine ⟨phare _,fun i j=>iff_of_false (Finset.notMem_empty _) (Finset.notMem_empty _),fun i=>?_,fun i=> (display (act p) _ _).1 (ruler p i B Y),fun _ _=> Iff.rfl,?_⟩
   · apply (display (act p) _ _).1; unfold sailP; change halo _ (plank (sashP (V _) _) _ _)=_; rw [show plank (sashP (V i) _) _ _=_ from ruler p i B Y]; exact halo_image (30 * radiusB τ) t b' _ -- defeq
   intro i X A
   let Q':=trade (copies N (haze p q χ)); change _ = Q'.passL (NormedSpace.exp _-1); rw [map_sub,map_one, NormedSpace.map_exp Q'.passL Q'.phare]; symm; apply congr_arg₂ (·-·) _ rfl; apply congr_arg
   apply rayTrade _ (copies_unitary _ _ (trail hh))
   let a:=haze p q χ
   have hf: Warrant (raise G p) χ q:=by rw [hygiene]; exact hh
   have he (U:Grid c): sheetP Γ B i (sky p U)=a*sheetP Γ B (V i) U*star a:=by
       apply whist; intro x y
       unfold sheetP a haze Revolve.hues; rw [stack,cell_ride_right,cell_ride_left,stack,monotype,monotype]
       have hb := oak hp.1 hf i.1 i.2 x y B U; rw [hygiene] at hb
       rw [hb]; change sale i.1 x y (_* _*star _) = _ * sale (Strut.act p i.1) (Strut.act p x) (Strut.act p y) (chipK (Strut.act p i.1) B Γ (Strut.act p x) (Strut.act p y) (hoops G p i.2) (Kit.settled U)) *star _ -- edit
       have hv (x:Site c): (sun G|>.shiftP p) x=Strut.act p x:= by change Strut.act (raise (singleR c) p) x=_; rw [hygiene]
       simp only [hv, sale,EmbeddingLike.apply_eq_iff_eq,Matrix.mul_smul,Matrix.smul_mul, lightP,id_eq]
   change copies N (-(sheetP Γ B i (sky p A)- sheetP Γ B i (lowC Y.ratio (sky (raise Y.ratio p) X))))=_; rw [he,Port.pulled,he,← Matrix.sub_mul,← Matrix.mul_sub,← Matrix.neg_mul,← Matrix.mul_neg]; exact Sway.podium ..
end YM.QCD.Villa

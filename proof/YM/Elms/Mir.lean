import YM.Elms.Foyer
/-! # Reflection powers.Fuel and seats in the rank-evaluation.
Up to all finite extents. Keep flag warranties of the original entry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
local notation "τ"=> su.probHaar
local notation "s"=>Signed.mirror a
local notation "V"=> Lat.Fields n 6
local notation "F"=> Insertion n 6
local notation "E"=>Patria.Exposure.eyeP n a
local notation "O"=>axisT a o
local notation "P"=> landsE n o w
noncomputable def sun(w:Walk): Walk:=w.map (·.rotate (Signed.mirror a))
local notation "W'"=>sun a w
lemma tiltedP : expandAt (wrap n o) (pull s 0 U)=pull s 0 (expandAt (wrap n O) U):= by rw [expandAt_pull]; simp [axisT,affine,wrap_signed]
lemma merit : haloW n o w (pull s 0 U)=haloW n O W' U:=by unfold haloW; rw [tiltedP, Lattice.travel_pull]; simp [affine,sun]
lemma endMotion : stop (0:Cover) W'=axisT a (stop 0 w):=by
    have ht(x:Cover)(w:Walk): stop (axisT a x) (sun a w)=axisT a (stop x w):=by induction w generalizing x <;> simp_all [sun,axisT,stop,Step.vec_rotate,← Signed.act_add] -- namespace tactic
    rw [← ht]; simp [axisT]
lemma cappedY : capEdge O W'=axisT a (capEdge o w) :=by simp_rw [capEdge,endMotion,axisT,Signed.act_add]
lemma pole : landsE n O W'=axisT a P:=by unfold landsE; rw [cappedY]; exact (wrap_signed ..).symm -- maybe orientation
local notation "Ω"=> stripe n o w (pull s 0 U)
local notation "X"=>stripe n O W' U
def emberZ (n:Side)(o:Cover)(w:Walk):= Cylinder.ap n ((s).act (Cylinder.sheet (landsE n o w)))
local notation "bV"=>emberZ a n o w
lemma stripe_t : bV • Ω= X:=by
     unfold stripe; rw [merit,smul_smul,cappedY]; congr 1; rw [mul_comm]; exact Ferry.sheet_launch ..
lemma glassP (q:Bool)(i j:Dike): (starRingEnd ℂ) (peggle q Ω i j) * bV= peggle (!q) X i j:=by
   rw [←stripe_t]; cases q with
   | false=> simp only [peggle,Bool.false_eq_true, ↓reduceIte,Bool.not_false,star_smul, emberZ,Ferry.ap_star,Matrix.transpose_apply, Matrix.smul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]; rw [mul_comm]; rfl
   | true=> simp only [peggle, if_true, Bool.not_true, Bool.false_eq_true,if_false,Matrix.transpose_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.smul_apply]; change star (star _) * _=_; rw [star_star,mul_comm]; rfl
lemma rotorP (p:Bool): Commute (peggle (!p) X) (ivZ a p):=by
    cases p with
    | false=>
       change (star X).transpose * (-(mL (gamma a)).transpose)= (-(mL (gamma a)).transpose)*(star X).transpose; rw [mul_neg,neg_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul]; exact congr_arg (fun i:ΔM=> -i.transpose) (starstripe U O W' _).symm.eq -- starstripe arg order check
    | true=> exact (stripe_wave U O W' (gamma a)).neg_right
lemma conveyor_at (q:Bool)(i:Dike): unia a (burnish w q i n o) U= (∑ j:Dike, ivZ a q i j • burnish W' (!q) j n O) U:=by
   rw [heroY,ContinuousMap.sum_apply]; simp only [ContinuousMap.smul_apply]; change tilt E (beams q n o w (pull s 0 U) i)=∑ j:Dike, ivZ a q i j • beams (!q) n O W' U j; unfold beams; simp_rw [map_sum,map_smulₛₗ,hemis];
   have hp(f: Dike→V) : ∑ j:Dike, (starRingEnd ℂ) (peggle q Ω i j) • bV • ∑ v:Dike, ivZ a q j v • f v = ∑ v:Dike, ivZ a q i v • ∑ j:Dike,peggle (!q) X v j • f j :=by
       simp_rw [smul_smul (starRingEnd ℂ _) bV, glassP, Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]; conv_rhs=>rw [Finset.sum_comm]
       refine Finset.sum_congr rfl (fun j _=>?_); rw [←sum_smul,← sum_smul]; exact congr_arg (fun z:ℂ=>z • f j) (congr_fun (congr_fun (rotorP U o w a q).eq i) j)
   simpa only [emberZ, pole] using hp (fun i:Dike=> lineT (!q) (place (axisT a (landsE n o w)) i))
lemma conveyor (q:Bool)(i:Dike): unia a (burnish w q i n o)= ∑ j:Dike, ivZ a q i j • burnish W' (!q) j n O:=ContinuousMap.ext (fun U=>conveyor_at U o w a q i)
lemma crewP (q:Bool)(i:Dike): via a (burnish w q i)=∑ j:Dike,ivZ a q i j • burnish W' (!q) j:=by
   funext n o; change unia a (burnish w q i n (axisT a o))= _; rw [conveyor]; simp only [Finset.sum_apply,Pi.smul_apply]; rw [axis_sq]
lemma forgeA(p p':Slot)(r:ℝ)(hx:∀ U:CoverConfig su,p.eval (pull (Signed.mirror a) 0 U) = r • p'.eval U) (i:su.ColorIndex):via a (tendency p i) n o U=(r:ℂ) • tendency p' i n o U:=by
    change unia a (tendency p i n (axisT a o)) U=_; rw [heroY]; change tilt E ((slotted su p i _) • 1)=_; unfold slotted; rw [tiltedP,axis_sq,hx,map_smulₛₗ,tilt_one]; change star ((↑(r*(_:ℝ)):ℂ)) • _= (r:ℂ) • ((↑((p'.eval (expandAt (wrap n o) U) ) i):ℂ) • (1:Lat.Fields n 6)); rw [show ∀ k:ℝ,star (k:ℂ)=(k:ℂ) from fun k=> Complex.conj_ofReal _,Complex.ofReal_mul, mul_smul]; rfl
lemma forge (p:Slot)(i:su.ColorIndex): ∃ p',∃ r:ℝ, via a (tendency p i)= (r:ℂ) • tendency p' i:=by
    obtain ⟨q,r,hr,hg⟩:= Work.G06.slot_pull (G:=su) s p; exact ⟨q,r,funext fun n=>funext fun o=> ContinuousMap.ext (fun u=>forgeA u o a p q r hg i)⟩
-- Ind.span of words after.S.preserving.Separate transformations even/odd.U.
def phrase (g t:ℕ) := Submodule.span ℂ {x:Drape|∃ l:List Bough,x=leaflet l∧ gaugeI l=g∧fermI l=t}
variable {x y:Drape}{g t i j:ℕ}
lemma pagedB(l:List Bough):leaflet l∈phrase (gaugeI l) (fermI l):= Submodule.subset_span ⟨l,rfl,rfl,rfl⟩
lemma onePage:(1:Drape)∈phrase 0 0:=pagedB []
lemma miniPage (x:Bough):issue x ∈ phrase (luminos x) (tallyS x):=by have he:=pagedB [x]; simpa only [leaflet,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one, fermI,gaugeI,List.sum_cons,List.sum_nil,Nat.add_zero] using he
lemma pages_mul (h:x∈phrase g t)(hh:y∈phrase i j): x*y ∈ phrase (g+i) (t+j):=by
   refine Submodule.span_induction (p:=fun x _ => x*y∈_) ?_ (by simp) (fun x y _ _ hx hy=> by rw [add_mul]; exact Submodule.add_mem _ hx hy) (fun c a _ h=> by rw [_root_.smul_mul_assoc]; exact Submodule.smul_mem _ _ h) h
   rintro x ⟨l,rfl,hp,hL⟩; refine Submodule.span_induction (p:=fun y _=>leaflet l*y∈_) ?_ (by simp) (fun x y _ _ hx hy=>by rw [mul_add]; exact Submodule.add_mem _ hx hy) (fun c a _ h=> by rw [_root_.mul_smul_comm]; exact Submodule.smul_mem _ _ h) hh
   rintro y ⟨k,rfl,rfl,rfl⟩; refine Submodule.subset_span ⟨l++k,?_,?_,?_⟩ <;> first | simp [leaflet] | rw [← hL]; simp [fermI] | rw [← hp]; simp [gaugeI]
lemma miniBurn (q:Bool)(i:Dike)(w:Walk):burnish w q i ∈ phrase 0 1:=miniPage (.inr ⟨w,q,i.1,i.2⟩)
lemma miniSpin (v:Bough):via a (issue v)∈ phrase (luminos v) (tallyS v):=by
    cases v with
    | inl v=> change via _ (tendency v.1 v.2)∈ phrase 1 0; obtain ⟨p,r,h⟩:=forge a v.1 v.2; rw [h]; exact Submodule.smul_mem _ _ (miniPage (.inl (p,v.2)))
    | inr v=> change via _ (burnish v.wal v.q (v.i,v.u))∈ phrase 0 1; rw [crewP]; exact Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ _ (miniBurn (!v.q) i (sun a v.wal))) -- .. span overflow
lemma pages (l:List Bough): via a (leaflet l)∈ phrase (gaugeI l) (fermI l):=by
    induction l with
    | nil=> rw [show leaflet []=1 from rfl,via_one]; exact onePage
    | cons p l ih=>
       have ht:=pages_mul ih (miniSpin a p); rw [Nat.add_comm (gaugeI l),Nat.add_comm (fermI l)] at ht; rw [show leaflet (p::l)=issue p *leaflet l from rfl,via_rev]; exact ht
lemma shelf (h: x∈ phrase g t): Writing x g t:=by refine Submodule.span_induction (p:=fun x _=>Writing x g t) ?_ (Writing.zero ..) (fun _ _ _ _=> Writing.add) (fun i _ _ hx=>hx.scale i) h; rintro x ⟨l,rfl,rfl,rfl⟩; exact smokey l
lemma pagesVia (h:x∈phrase g t):via a x ∈ phrase g t:=by
    refine Submodule.span_induction (p:=fun x _=>via a x∈_) ?_ (by simp) (fun x y _ _ hx hy=>by rw [map_add]; exact Submodule.add_mem _ hx hy) (fun i x _ h=>by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ h) h; rintro y ⟨l,rfl,rfl,rfl⟩; exact pages a _
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.pagesVia

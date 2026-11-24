import YM.Profiles.Quills
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace Quills
variable {Q:Type}[Fintype Q](A:Type)[Fintype A] (q:I→Bool) (p:J→Bool) (P:Set (Finset J))(P₀:Set (Finset I))(r:I→J→Prop)(g:I→J→ℝ)(H:Pledge q p r P P₀)(s:Fin n→J)
local notation "X"=>Patio (A⊕Spine I)
local notation "Y"=> Patio (A⊕Spine J)
-- explicit predecessor lists for any eligible placement list. weights signs real & negative allowed.
abbrev Queue (s:Fin n→J) := ∀ (i:Fin n), To r (s i)
local notation "W"=> Queue r s
variable (u:(i:Fin n)→To r (s i))
noncomputable def attends (i:Fin n) : I:= (u i).val
noncomputable def beans := ∏ i:Fin n,(↑(g (attends r s u i) (s i)):ℂ)
local notation "K"=> crest s
local notation "T"=> findV r (crest s)
local notation "G"=> Sample.flame A q p T g
local notation "ρ"=> attends r s u
variable (ht:crest s∈P) (hp:Injective s)
local notation "A!"=> leaves A q p
include H
lemma style (e:Finset J)(he:e∈P)(hφ:crest s⊆e): (A!) (findV r e) g (quill A (armature q ρ))= beans r g s u • quill A (armature p s):=by
    induction n with
    |zero=>simp [beans, armature]
    |succ n ih=>
       let i₁:=(Fin.tail s); let U: Queue r i₁ :=fun j:Fin n=>u j.succ; have hI: crest i₁⊆ e:= (subset_insert (s 0) (crest i₁)).trans ((crest_next s) ▸ hφ)
       have hZ:= ih i₁ U hI; have hz :Fin.tail (attends r s u)= attends r i₁ U:=rfl; let G':= g (attends r s u 0) (s 0); have hP: beans r g s u=(G':ℂ)*beans r g i₁ U:=Fin.prod_univ_succ _; let F:= (A!) (findV r e) g
       rw [arm,arm,map_mul,map_mul,map_mul,hz,show F (quill A (armature _ _))=_ from hZ,leaving A q p (findV r e) g (attends r s u 0) (s 0) ((findG r H.mast _ _ he).2 ⟨hφ ((exists_fix ..).2 ⟨0,rfl⟩),(u 0).property⟩) (H.takes _ _ (u 0).property),hP,mul_smul_comm,smul_mul_assoc,mul_smul] -- rw order
include hp ht
lemma attends_well : Injective (attends r s u):=by
   intro a b h; apply hp; apply H.mast.sends _ (ρ b) _ _ ht (mem_image_of_mem s (mem_univ a)) (mem_image_of_mem s (mem_univ b)); exact h ▸ (u a).property; exact (u b).property
lemma usher :Melts r P (crest (attends r s u)) K:=by
    have ht1(i:Fin n): T (ρ i)=some (s i):=(findG r H.mast _ _ ht).mpr ⟨mem_image_of_mem s (mem_univ _), (u i).property⟩
    refine ⟨ht, ⟨?_,?_⟩,?_⟩
    · intro a ha b hb hx; obtain ⟨j,rfl⟩:=(exists_fix ρ a).1 ha; obtain ⟨k,rfl⟩:=(exists_fix ρ b).1 hb; rw [ht1,ht1] at hx; exact congr_arg ρ (hp (Option.some.inj hx))
    · intro a ha; obtain ⟨j,rfl⟩:=(exists_fix ρ a).1 ha; rw [ht1]; exact Option.some_ne_none _
    ext i; rw [frontM,exists_fix]; constructor; · rintro ⟨j,hj,htJ⟩; obtain ⟨u,rfl⟩:=(exists_fix ρ _).1 hj; rw [ht1] at htJ; exact ⟨_,Option.some.inj htJ⟩
    rintro ⟨j,rfl⟩; exact ⟨ρ j,(exists_fix ρ _).2 ⟨_,rfl⟩,ht1 _⟩
lemma onlyU : Injective (fun u:Queue r s=> crest (attends r s u)):=by
    intro u v h; funext i; apply Subtype.ext; let U:=attends r s u; let V:= attends r s v; change crest U=crest V at h; have hu:U i∈crest V:=h ▸ mem_image_of_mem U (mem_univ _); obtain ⟨j,hj⟩:=(exists_fix V _).1 hu
    have hv:s i=s j:=H.mast.sends _ (U i) _ _ ht (mem_image_of_mem s (mem_univ _)) (mem_image_of_mem s (mem_univ _)) (u i).property (show r (U i) _ from hj ▸ (v j).property)
    exact hj.symm.trans (congr_arg V (hp hv).symm)
omit hp
lemma acomodated (v:Finset I)(hv:Melts r P v K) : ∃ u:Queue r s,crest (attends r s u)=v:=by
    have he(i:Fin n) : s i∈front T v:=hv.2.2.symm ▸ mem_image_of_mem s (mem_univ _); choose A hA hQ using fun i=> (frontM T).1 (he i)
    let u(i:Fin n):To r (s i):= ⟨A i, ((findG r H.mast _ _ ht).1 (hQ i)).2⟩; refine ⟨u,?_⟩; ext i; rw [exists_fix]; constructor; rintro ⟨j,rfl⟩; exact hA j
    intro hi; obtain ⟨t,ht'⟩:=Option.ne_none_iff_exists'.1 (hv.2.1.2 i hi); obtain ⟨a,rfl⟩:=(exists_fix s _).1 (hv.2.2 ▸ (frontM T).2 ⟨i,hi,ht'⟩); exact ⟨a, hv.2.1.1 (hA _) hi ((hQ _).trans ht'.symm)⟩
include hp
lemma cosmos (x: Patio (A⊕Spine I))(htx:Polite q (crest ρ) x): numbered p A s (G x)= beans r g s u • numbered q A ρ x:=by
    have hP := style A q p P P₀ r g H s u K ht (Subset.refl _); let φ:= (A!) T g; apply cuts A p s hp
    change φ x.val=_; nth_rw 1 [Quills.charge A q _ x htx (attends_well q p P P₀ r H s u ht hp)]; rw [map_mul,show φ (quill A (armature _ _))=_ from hP]; unfold φ; rw [Sample.leaves, AlgHom.comp_apply, tarfib,blot_left,map_smul,mul_smul_comm,smul_mul_assoc]
lemma billSlide (x: X)(hX:ValidPieces A q Finset.univ x) : numbered p A s (G x)=∑ u:Queue r s, beans r g s u • numbered q A (attends r s u) x:=by
    let v (a:Finset I):= numbered p A s (G (Cupola.pick A q a x)); let ψ(u:Queue r s):=crest (attends r s u); let F₁:=Finset.univ.filter fun s:Finset I=>s∈((univ:Finset I).powerset:Set (Finset I)); have hC:F₁=Finset.univ:= by unfold F₁; ext i; simp
    nth_rw 1 [hX.wholeV]; rw [map_sum,map_sum]; change ∑ i∈F₁,v i=_; rw [hC, ← sum_subset (s₁:=univ.image ψ) (subset_univ (univ.image ψ)) (f:=v) ?_, sum_image (onlyU q p P P₀ r H s ht hp).injOn]; swap
    · intro i _ he; unfold v; let U:=Cupola.pick A q i x; have hX:= choseTuft A q i x; by_cases H': Fare T i
      · have hf : Polite p (front T i) (G U):=by obtain ⟨c,hC,h⟩:= flameStake A q p _ g (hym q p r H _ ht) i U hX H'; exact ⟨_,h.symm⟩
        change signG p s • pluck A (burst p K) (G U)=0; rw [show pluck A (burst p K) (G U)=0 from hf.spectral _ (fun hk=>?_),smul_zero]; obtain ⟨u,h⟩:= acomodated q p P P₀ r H s ht i ⟨ht,H',(burstUnique p hk).symm⟩; exact he (mem_image.mpr ⟨_,mem_univ u,h⟩)
      rw [latentF A q p _ g (hym q p r H _ ht) i U hX H',map_zero]
    refine sum_congr rfl fun u _=>?_ ; let a:=ψ u; unfold v; rw [show numbered p A s _= _ from cosmos A q p P P₀ r g H _ u ht hp _ (choseTuft A q a x)]; apply congr_arg; change signG q _ • pluck A _ (Cupola.pick A q _ x) = signG q _ • _; apply congr_arg; rw [Cupola.pick,many,if_pos rfl]; rfl
end Quills
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Quills.billSlide

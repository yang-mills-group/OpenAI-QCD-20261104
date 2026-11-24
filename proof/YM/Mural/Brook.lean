import YM.Mural.Refi
import YM.Mural.Rent
/-! # pluck projection under grants. Budget resynchronize and read charges including canonical base. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon
variable {f c:Side}{j k d:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
variable {I E:Type}{N:ℕ} (Z:PrintR f N Rank I E) (D₁ D₂: Grid f→ Mat)(z:ℂ)
local notation "Ψ"=> Tine f N Unit
local notation "Tz"=> trestle Z D₁ D₂ z
local notation "Z★" i=>PrintR.regE Tz i
local notation "Y★" i=> PrintR.regK Tz i
local notation "κ"=>Cove.Keys f N
local notation "R"=> Ribbon.Spine Unit
local notation "Uκ"=> rootR (Spine Unit) (Cove.Keys f N)
open Push.AbsoluteSums Film
variable (U:Grid f)(O:BudgetPoint){w e t η:ℝ}(S:Support f) (V:Unit→Site f)
variable {A:Type*}{J:Type} (Q:Lat.Frame f→ Delta Rank) (P:Patron.Rail f N J)(T:Grid f→ EvenA f N) (hp: Summable (fun i=> ‖P.warp i U‖))(hP: Z.Fides V S O Q)
local notation "K!"=> R
noncomputable def fur (i:Option Rank):= relativeE N (Z.regE i) (Z.regK i) P T O.threshold U
local notation "Vℓ" i=> fur Z U O P T i
open NormedSpace
include hp hP
lemma roh : (Vℓ none)=Uκ (exp (T U)*heartK P O.threshold U):=by
    let Z':=Z.regE none; let V':=Z.regK none; let X:= fun _:Site f=> (1:su.El); let G:=X; have hR: Reel.rope Z' O.threshold U=0:= by unfold Reel.rope; simp_rw [show ∀ i,Z'.mist O.threshold i U=0 from fun i=> (hP.tinted G).neutral i U]; rw [tsum_zero]
    let Ξ:= Film.reports N V' P O.threshold U
    have hz (i:E): V'.mark i U=0:=(hP.rise G).unit i U; let χ:= Film.addressSets N V' P; let f i:= Film.spruced N V' P i U; let A:=RG.flags O.threshold U; let v i:= Plate.roof χ f A i; let g:= (Uκ).toLinearMap.toContinuousLinearMap
    have he(j:Finset (J⊕ E))(i:E)(h:Sum.inr i∈j): v j=0:= by unfold v Plate.roof; split; exact prod_eq_zero h (hz _); rfl
    let e:J↪J⊕E:=Function.Embedding.inl; let φ(s:Finset J):= s.map e; have hs:Function.support v⊆ Set.range φ:=by
       intro i hv
       have h :∀ j∈ i,j∈Set.range e:=by
            rintro (j|j) hj; · exact ⟨j,rfl⟩
            exact False.elim ((show v i≠0 from hv) (he _ _ hj))
       refine ⟨i.preimage e e.injective.injOn, Finset.ext (fun j=> ⟨?_,?_⟩)⟩
       · intro hp; obtain ⟨k,hpk,rfl⟩:=Finset.mem_map.mp hp; exact mem_preimage.mp hpk
       intro hp; obtain ⟨p,rfl⟩:=h j hp; exact Finset.mem_map.mpr ⟨p,mem_preimage.mpr hp,rfl⟩
    have ht(i:Finset J):v (φ i)=(Uκ) (Ruby.tK P O.threshold U i):=by
        have h:Arm χ A (φ i) ↔ Arm P.addr A i:=by
             apply and_congr
             · constructor
               · intro h x hx y hy hv; exact h (Finset.mem_map.mpr ⟨x,hx,rfl⟩) (Finset.mem_map.mpr ⟨y,hy,rfl⟩) (show e x≠e y from e.injective.ne hv)
               intro h x hx y hy hq; obtain ⟨x,hX,rfl⟩:=Finset.mem_map.mp (show x∈φ i from hx); obtain ⟨y,hY,rfl⟩:=Finset.mem_map.mp (show y∈φ i from hy); exact h hX hY (fun he=>hq (he ▸ rfl))
             have hm : (φ i).biUnion (fun x=> (χ x).inv)=i.biUnion (fun x=>(P.addr x).inv):=by
                  ext x; constructor
                  · intro h; obtain ⟨j,hj,hT⟩:=mem_biUnion.mp h; obtain ⟨p,hp,rfl⟩:= Finset.mem_map.mp hj; exact mem_biUnion.mpr ⟨p,hp,hT⟩
                  intro h; obtain ⟨p,hp,h⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨e p, Finset.mem_map.mpr ⟨p,hp,rfl⟩, h⟩
             rw [hm]
        rw [termsK]; unfold v Plate.roof; rw [h]; split; swap; · exact (map_zero _).symm
        unfold φ; rw[prod_map,map_prod]; rfl
    have hh:Summable (Ruby.tK P O.threshold U):= by simp_rw [show Ruby.tK P O.threshold U=Plate.roof _ _ _ from funext (termsK P O.threshold U)]; exact Plate.rum _ _ _ hp
    have hx: Ξ= (Uκ) (heartK P O.threshold U):= (((map_injective e).tsum_eq hs).symm.trans (tsum_congr ht)).trans (g.map_tsum hh).symm
    unfold fur relativeE; rw [hR,add_zero,← map_exp (Uκ) ((Uκ).toLinearMap.toContinuousLinearMap.continuous),show reports N V' P O.threshold U= _ from hx]; simp [map_mul]
variable (hK:∀ i:Option Rank,Summable fun j=> ‖(Z.regE i).mist O.threshold j U‖)(hv:∀ i:Option Rank,Summable fun j=> ‖Z.etaK i j U‖)(hE:∀ i:Option Rank,Summable fun j=> ‖Reel.mist (PrintR.regE (trestle Z D₁ D₂ z) i) O.threshold j U‖)(hw:∀ i:Option Rank,Summable fun j=> ‖(trestle Z D₁ D₂ z).etaK i j U‖)
local notation "u" i=>fur (trestle Z D₁ D₂ z) U O P T i
lemma rosa : pluck (Keys f N) sD (Vℓ none)=0:=by rw [roh Z U O S V Q P T hp hP]; let x:=exp (T U)*heartK P O.threshold U; change scrape _ sD (fiber (Spine Unit) x.val)=_; rw [← Ribbon.quiet, stakesX, if_neg ((show sD.Nonempty from ⟨(((),false),0),mem_univ _⟩).ne_empty)]
include hK hv hE hw
lemma stanzas (i:Rank): pluck κ sD (u (some i))= z • ∑ j:Rank, doll (D₁ U) (D₂ U) i j • pluck κ sD (Vℓ (some j)):=by
    obtain ⟨hh,hL⟩:= silhouettes z Z D₁ D₂ U O V S Q hP P T hK hv hE hw hp; let A:=zoneD (D₁ U) (D₂ U) z; let v(k):=fur Z U O P T k
    let f(k):= A (some i) k • v k; have he: (u (some i))= ∑ j,f j:= hh (.some i); rw [he,map_sum,Fintype.sum_option]; have hX(T): pluck κ sD (f T)=_:= map_smul (pluck κ sD) (A (some i) T) (v T); -- result metavariable
    rw [hX none,show pluck κ sD (v none)=_ from rosa Z U O S V Q P T hp hP,smul_zero,zero_add,Finset.smul_sum]; exact sum_congr rfl fun j _=> (hX (.some j)).trans (mul_smul ..)
lemma primus (i:Option Rank): pluck κ ∅ (Vℓ i)=(exp (T U)*heartK P O.threshold U).val:=by
    have hx:= (silhouettes z Z D₁ D₂ U O V S Q hP P T hK hv hE hw hp).2.bonds i; have hg:=congr_arg Subtype.val hx; rw [show relativeE N (Z.regE none) (Z.regK none) P T O.threshold U=_ from roh Z U O S V Q P T hp hP] at hg
    refine Eq.trans ?_ (hg.trans (congr_arg Subtype.val (Cupola.off (Spine Unit) _))); exact (Cupola.revive R _).symm
end YM.QCD.Comet
#print axioms YM.QCD.Comet.stanzas
#print axioms YM.QCD.Comet.primus

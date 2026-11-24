import YM.Mural.Relay
import YM.Mural.Quarter
/-! # exit schedules from aligned rails. -/
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 520000
noncomputable section
namespace YM.MassiveQCD.Plette
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace Push.AbsoluteSums
open Plate Stitch Tablet Ribbon Lattice Wilson Lat RG Twist PaletteT
open scoped BigOperators Topology Classical ContDiff
variable {c:Side}(N:ℕ)(p:Unit→Site c)(q:Unit→Bool)(P:Set (Finset Unit))(t:ℝ){I E J:Type} [Fintype I](Y:Patron.Rail c (ample N Unit) E)
open Plate.Film Patron
variable (S:Support c){b u v r τ:ℝ}
variable (R:Option I→ E→ Grid c→ EvenA c (ample N Unit))(H:Delta I)(g:Lat.Frame c)
local notation "T'"=> zone N p P Y S
noncomputable def sphere (i:Option I) (j:zone N p P Y S)(U:Grid c) : Patio (Keys c N⊕Spine Unit):=Cupola.pick (Keys c N) q j.val.snd.val (withdraw N p t (R i j.val.1 U)) -- missing j
local notation "Fp" => season N p q P t Y S
local notation "RF"=>sphere N p q P t Y S R
local notation "Tx" i=> verse Fp RF i
local notation "K"=> Keys c N
lemma onstage (i:Option I): (Tx i)= season N p q P t (pathsV N Y (R i)) S:=rfl
lemma fragment (Wc:Lat.Frame c)(x:Patio (Keys c N⊕Spine Unit))(l:Finset Unit): dance Unit Wc N (Cupola.pick (Keys c N) q l x)= Cupola.pick (Keys c N) q l (dance Unit Wc N x):=by
     apply pluckVisible; intro i; rw [inkdance,inkdance,partColor]; unfold Cupola.pick; rw [many,many]; split; exact (partColor ..).symm; exact map_zero _
variable (hz:Parade N p t Y R q S g H)(hp:∀ i,(pathsV N Y (R i)).Reg b)(hf:0<t)
include hz hp hf
lemma octave : JointK p q Fp RF S b g H:=by
    refine ⟨fun i=>by
        rw [onstage]; exact readyVol N p q P t _ S (hp i), fun i V=>?_,fun i U=>?_⟩
    · obtain ⟨⟨i,hi⟩,hz'⟩:= i -- inspect
      let Z:= withdraw N p t; let J:=hz.style i V; let v:=J.loose.plain; let hT:=hi.val
      have hξ:hT.Nonempty:=(mem_filter.mp hi.2).2.2.1
      apply Subtype.ext; change (Cupola.pick (Keys c N) q hT (withdraw N p t (R none i V))).val=0; rw [show (Cupola.pick K q hT (withdraw N p t (R none i V))).val=_ from choice ..] -- unsure syntax Cupola.pick = chooseBlade then choice, print
      rw [show pluck K _ _=0 from v.spectral _ (fun he=> hξ.ne_empty (burstUnique q he)),map_zero]
    let j:=i.val.fst; let U':= gauge g U; let x i:=withdraw N p t (R i j U); let y i:= withdraw N p t (R i j U'); let Z:=Cupola.pick (Keys c N) q i.val.2.val
    have hS:Binds H (dance Unit g N) y x:= talk N p t g H hf _ _ (hz.style j U') (hz.verse j U)
    intro a; change (dance Unit _ N) (Z (y a))=aggregate _ (fun i=>Z (x i)); rw [show dance Unit g N (Z _)=Z _ from fragment N q g (y a) _, hS a]; unfold aggregate; rw [map_sum]; exact sum_congr rfl fun i _=>map_smul ..
omit hz hf hp

-- E companion
variable (Z:Gem c (ample N Unit) E)(X: Option I→E→Grid c→ EvenA c (ample N Unit))(Ω:E→ Finset Unit)(z:ℝ)
noncomputable def gem_h (i:Option I): Gem c (ample N Unit) E:= {Z with view:=X i}
noncomputable def spit_h (i:Option I) (j:Reel.Answer N p Z Ω P): Grid c→Patio (Keys c N⊕Spine Unit):=(Reel.render N p t z (gem_h N Z X i) Ω P).mark j
variable (ht:0<t)(he:straight H)(hh:∀ i,(gem_h N Z X i).Gather)(hw:∀ i j V,Mint N p t q (Ω j) ((gem_h N Z X i).view j V))(hx:∀ i,(Ω i).Nonempty→ S⊆ (Z.addr i).support)(hG:∀ j V, Binds H (actC (ample N Unit) g) (fun i=> letters (gem_h N Z X i) b (gauge g V) j) (fun i=>letters (gem_h N Z X i) b V j) ∧ Dealers N p t q (fun i=>letters (gem_h N Z X i) b V j))
local notation "φ"=>Reel.render N p t z Z Ω P
local notation "χ"=>spit_h N p P t Z X Ω z
lemma spotlight (i: Option I): script φ χ i= Reel.render N p t z (gem_h N Z X i) Ω P:=rfl
lemma spotL (i:Option I)(j:Reel.Answer N p Z Ω P)(v:Grid c): Reel.mist (script φ χ i) b j v=(Plate.turn Unit z) (withdraw N p t (letters (gem_h N Z X i) b v j.val)):= Reel.currentS N p t z (gem_h N Z X i) Ω P v j
lemma disap {A:Type}[Fintype A](s:Finset Unit)(he:s.Nonempty)(x: Patio (A⊕Spine Unit))(h: Polite q s x)(hr:Polite q ∅ x):x=0:=by
      apply Subtype.ext; exact h.exact.symm.trans ((congr_arg _ (hr.spectral _ (fun hv=>he.ne_empty (burstUnique q hv)))).trans (map_zero _))
lemma funda (x y:Option I→ Patio (Keys c N⊕Spine Unit))(hp:Binds H (dance Unit g N) x y): Binds H (dance Unit g N) (fun i=>turn Unit z (x i)) (fun i=>Plate.turn Unit z (y i)):=by
    let D:= turn Unit (D:=K) z; intro i
    have ht: (dance Unit g N) (D (x i))=D (dance Unit g N (x i)):= by rw [inkdance,inkdance]; exact (Plate.freeT z (x i) g).symm
    refine ht.trans ((congr_arg D (hp i)).trans (?_)); unfold aggregate; rw [map_sum]; exact sum_congr rfl fun _ _=>map_smul ..
include ht he hh hw hx hG
lemma originR : JointE p q φ S b g H χ:=by
    let f(j:E) U i:=letters (gem_h N Z X i) b U j; let T:= turn Unit (D:=K) z; let D:= withdraw N p t
    have hu (i:Option I)(j:Reel.Answer N p Z Ω P)(v:Grid c): Reel.mist (script φ χ i) b j v=T (D (f j.val v i)):=spotL N p P t Z X Ω z i j v -- v order
    refine ⟨fun i=>?_ ,fun i V=>?_,fun i V j=>?_⟩
    · exact began N p z t q (gem_h N Z X i) Ω P S (hw i) (hh i) hx ht
    · rw [hu]; suffices h:D (f i.val V none)=0 by rw [h,map_zero]
      have hp: Polite q ∅ (D (f i.val V none)):= (hG i.val V).2.loose.plain; have he':= (Reel.mast (t:=b) N p q t (gem_h N Z X (none:Option I)) Ω (hw _) V i.val).shows
      exact disap q (Ω i.val) i.2.2.1 _ he' hp
    let W:=gauge g V; let Y':=X; have hn:= talk N p t g H ht _ _ (hG i.val W).2 (hG i.val V).1
    let x i':= D (f i.val W i'); let y i':= D (f i.val V i')
    have hH:= funda N H g z x y hn j
    exact ((congr_arg (dance Unit g N) (hu j i W)).trans hH).trans (congr_arg (aggregate (fun j'=>H j j')) (funext fun j'=> (hu j' i V).symm))
end YM.MassiveQCD.Plette
#print axioms YM.MassiveQCD.Plette.octave
#print axioms YM.MassiveQCD.Plette.originR

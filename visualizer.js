console.log('\n'); // newline in console


// Getting the note information from Forge
nexts = Note.join(nextnotes).tuples().map(n => n.atoms()[0]); // all the nextnotes
starter = Note.atoms().filter(x => !nexts.includes(x))[0]; // gets the 1st note by virtue of not being in the nextnotes

ordered = [starter]; // start the array
for (i = 1; i != Note.atoms().length; ++i ) {
  ordered.push(ordered[i-1].join(nextnotes).tuples()[0].atoms()[0]); // add each next note atom in order
};

// for each note atom, we decompose into:
// [pclass, octave, noteLength, accompanyP, accompanyO]
noteInfo = ordered.map(n => [n.join(pclass).tuples()[0].atoms()[0].id(), 
  n.join(octave).tuples()[0].atoms()[0].id(), n.join(noteLength).tuples()[0].atoms()[0].id(), 
  n.join(accompanyP).tuples()[0].atoms()[0].id(), n.join(accompanyO).tuples()[0].atoms()[0].id()]);


// Music/audio processing
const pitches = {C: 261.63, Csharp: 277.18, D: 293.66, Eflat: 311.13, E: 329.63, F: 349.23, 
  Fsharp: 369.99, G: 392.00, Gsharp: 415.30, A: 440.00, Bflat: 466.16, B: 493.88}; // pitch dictionary

var ourContextMain = new AudioContext(); // must initialize 1 universal context for main audio nodes
var ourContextAccompany = new AudioContext(); // must initialize 1 universal context for accompanying audio nodes
const lengthModifier = 0.375; // converts length to seconds

function playTone(freqMain, freqAccompany, startTime, endTime) {
  tempOscillatorMain = ourContextMain.createOscillator(); // need a new oscillator every time
  tempOscillatorMain.frequency.value = freqMain; // set the frequency of the oscillator
  tempOscillatorMain.connect(ourContextMain.destination); // must connect oscillator so we can hear
  tempOscillatorMain.start(startTime); // start time
  tempOscillatorMain.stop(endTime); // end time
  
  // accompaniment code (essentially duplicated from main)
  tempOscillatorAccompany = ourContextAccompany.createOscillator();
  tempOscillatorAccompany.frequency.value = freqAccompany;
  tempOscillatorAccompany.connect(ourContextAccompany.destination); 
  tempOscillatorAccompany.start(startTime);
  tempOscillatorAccompany.stop(endTime);

}

function playTheNotes(noteScore) {
  currAccTime = 0; // useful for choosing start/end times
  startedTime = ourContextMain.currentTime; // initialize start time
  console.log(noteScore); // debugging & gives info on notes being played
  for (i = 0; i != noteScore.length; ++i) {
    let n = noteScore[i]; // n is a particular note array
    let currPitchM = n[0].substring(0, n[0].length - 1); // removes the pesky trailing "0" from "C0", for example
    let octaveM = parseInt(n[1]); // octave
    let freqM = pitches[currPitchM] * (2 ** (octaveM - 1)); // every octave higher doubles the frequency

    // accompaniment code (very similar to main)
    let currPitchA = n[3].substring(0, n[3].length - 1);
    let octaveA = parseInt(n[4]);
    let freqA = pitches[currPitchA] * (2 ** (octaveA - 1));

    let currLength = parseInt(n[2]) * lengthModifier; // convert note length to seconds
    playTone(freqM, freqA, startedTime + currAccTime, startedTime + currAccTime + currLength); // careful tone playing
    currAccTime += currLength; // update accumulated time for timing purposes
  }
}

playTheNotes(noteInfo); // finally play everything!
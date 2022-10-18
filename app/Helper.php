<?php

namespace App;

use Twilio\Rest\Client;

class Helper
{
    public static function sendWhatsapp( $mobile_no , $message)
    {
        $account_sid = env ( 'TWILIO_SID' );
        $account_token = env ( "TWILIO_TOKEN" );
        $sending_number = env( "TWILIO_WHATSAPP" );
        $twilio_client = new Client( $account_sid , $account_token );

        $twilio_client->messages->create( "whatsapp:" . $mobile_no , array (
            "from" => "whatsapp:" . $sending_number ,
            "body" => $message
        ) );

    }

    public static function shortUrl( $url )
    {
        try {
            $client = new \GuzzleHttp\Client();
            $response = $client->request('POST', 'https://api.short.io/links/public', [
                'headers' => [
                    'Authorization' => env('SHORTIO_API_KEY'),
                    'Content-Type' => 'application/json'
                ],
                'json' => [
                    'originalURL' => $url,
                    'domain' => 'go.alphaalerts.io'
                ]
            ]);

            $data = json_decode($response->getBody()->getContents());

            return $data->shortURL;

        } catch ( \Exception $e ) {
            return $url;
        }

    }
}
